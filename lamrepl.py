#!/usr/bin/env python

# Lambda terms are either:
# - ("var", x, i)
#   for the variable with name `x' and disambiguation index `i'
#
#   disambiguation indices are for when you have a variable name that is bound
#   multiple times, as in (\x.\x. x). By convention the variable `x' refers to
#   the innermost binding, but during substitution on open terms, we can violate
#   this convention. So instead we give each variable an index indicating how
#   many binders for that name to "jump over". This is essentially DeBruijn
#   indexing. By convention, a bare variable name indicates an index of 0. eg.
#   (\x.\x. x) is more properly (\x.\x. x_0) and is alpha-equivalent to (\x.\y.
#   y). On the other hand, (\x.\x. x_1) is alpha-equivalent to (\x.\y. x).
#
# - ("app", f, g)
#   for (f g), that is, f applied to g
#
# - ("lam", x, e)
#   for (\x. e)
#
# - ("val", v[, name[, prec, fix]])
#
#   for an embedded value. any python value will do. If present, `name' is used
#   for pretty-printing. Calling an embedded value in the lambda calculus will,
#   unsurprisingly, call it in Python. Note that this means it had better be
#   unary; if you want multiarg embedded functions you must curry manually.
#
#   If present, prec and fix indicate that this is an infix operator with the
#   given precedence and fixity.

# ---------- UTILITY ----------
class LamError(Exception): pass
class Malformed(LamError): pass

def expect(v, pytyp = None):
    if pytyp is None: return v
    name = pytyp.__name__
    if v[0] != 'val':
        raise Stuck('expected %s, but got lambda term' % name)
    elif pytyp and not isinstance(v[1], pytyp):
        raise Stuck('expected %s, but got %s' % (name, type(v[1]).__name__))
    else:
        return v[1]

def embed(x, *args): return ('val', x) + args

def embed_func(argtypes, func, *extras):
    assert argtypes
    if len(argtypes) == 1:
        return embed(lambda x: func(expect(x, argtypes[0]))) + extras
    else:
        f = lambda x: embed_func(argtypes[1:], (lambda *args: func(x, *args)))
        return embed_func([argtypes[0]], f, *extras)


# ---------- PRETTY-PRINTER ----------
# positions:
# - 0: whole expression (immediately inside parens, lambda, or toplevel)
# - 1: in functional position
# - 2: in argument position
def pretty(e, pos = 0):
    typ = e[0]

    if typ == 'var':
        (typ, name, index) = e
        if index > 0:
            return '%s_%s' % (name,index)
        else:
            return name

    elif typ == 'app':
        s = '%s %s' % (pretty(e[1], 1), pretty(e[2], 2))
        if pos == 2:
            # in right app, need parens
            s = '(' + s + ')'
        return s

    elif typ == 'lam':
        (typ, var, body) = e
        s = '\%s. %s' % (var, pretty(body, 0))
        if pos:
            # in application, need parens
            s = '(' + s + ')'
        return s

    elif typ == 'val':
        if len(e) >= 3:
            # value with special name
            if len(e) > 3:
                # infix operator
                return '(' + e[2] + ')'
            return e[2]
        return repr(e[1])

    else:
        raise Malformed('bad lambda-calculus term')


# ---------- PARSER ----------

# Can parse numbers and strings as embedded python values. If you give a
# dictionary for macros, it will parse variable names in "macros" as whatever
# they map to. This means they should map to lambda terms!

class ParseError(LamError): pass
class ParseEnd(ParseError): pass
class ParseEmpty(ParseEnd): pass
class ParseClose(ParseEnd): pass

import re
res_var = '([a-zA-Z_][a-zA-Z_0-9]*)'
re_var = re.compile(res_var)
re_lamopen = re.compile(r'\\\s*(' + res_var + r')\s*\.')
re_popen = re.compile(r'\(')
re_pclose = re.compile(r'\)')
re_int = re.compile(r'-?[0-9]+')
re_str = re.compile(r'"[^"\\]*"|'r"'[^'\\]*'")

def parse(s, macros=None):
    p = Parser(macros = macros)
    return p.parse(s)

class Parser(object):
    def __init__(self, macros=None):
        self.macros = macros or {}
        self.infixes = {k: v for k,v in self.macros.iteritems()
                        if len(v) > 3}

    def parse(self, s):
        (x, s) = self.parse_whole(s)
        if s.lstrip():
            raise ParseError('junk at end of input: ' + s)
        return x

    def parse_whole(self, s):
        s = s.lstrip()
        if not s: raise ParseEmpty('unexpect end of input')

        m = re_lamopen.match(s)
        if m:
            argname = m.group(1)
            (body, s) = self.parse_whole(s[m.end():])
            return (('lam', argname, body), s)

        # see if the whole thing is just one infix operator; then we can return
        # it. this allows eg. (+) for the + operator.
        (o,snew) = self.parse_oper(s)
        snew = snew.lstrip()
        if o and (not snew or re_pclose.match(snew)):
            return o, snew

        return self.parse_app(s)

    def parse_app(self, s):
        e, s = self.parse_one(s)
        exps = [e]

        while True:
            (oper, s) = self.parse_oper(s)
            try:
                (arg, snew) = self.parse_one(s)
            except ParseEnd:
                if oper is None: # application
                    break
                raise
            else:
                # push operator onto stack
                exps.extend([oper,arg])
                s = snew

        def precfix(x):
            if x is None: return 0, -1
            else: return x[3:]

        # parse the expression list according to precedence.
        def pop_expr(prec, fixity):
            subexps = []
            while len(exps) >= 2:
                nextprec, nextfix = precfix(exps[-2])
                if nextprec > prec:
                    # next op binds looser than us.
                    break
                elif nextprec < prec:
                    # next op binds tighter than us
                    exps.append(pop_expr(nextprec, nextfix))
                else:
                    # next op has our precedence.
                    if nextfix != fixity:
                        raise ParseError(
                            "cannot mix operators of same precedence but " +
                            "different fixity")
                    subexps.append(exps.pop()) # argument
                    subexps.append(exps.pop()) # operator

            subexps.append(exps.pop()) # final argument

            def app(op, arg1, arg2):
                if op is None:
                    return ('app', arg1, arg2)
                else:
                    return ('app', ('app', op, arg1), arg2)

            # okay, now we must parse subexps, which is an interleaved list of
            # exps and operators of our fixity and precedence, in order.
            if fixity == 0 and len(subexps) > 3:
                raise ParseError("bad use of nonassociative infix operators")

            if fixity < 0:
                # left-associative
                exp = subexps.pop()
                while subexps:
                    op = subexps.pop()
                    arg = subexps.pop()
                    exp = app(op, exp, arg)
            else:
                # right-associative
                subexps.reverse()
                exp = subexps.pop()
                while subexps:
                    op = subexps.pop()
                    arg = subexps.pop()
                    exp = app(op, arg, exp)
            return exp

        return (pop_expr(float("+inf"), 0), s) # hack

        # exp = exps.pop()
        # while exps:
        #     oper = exps.pop()
        #     (prec, fixity, val) = oper or (

    def parse_oper(self, s):
        s = s.lstrip()
        for (name, op) in self.infixes.iteritems():
            if s.startswith(name):
                return (op, s[len(name):])

        oper = None             # application
        return (oper, s)

    def parse_one(self, s):
        s = s.lstrip()
        if not s: raise ParseEmpty('unexpected end of input')

        m = re_int.match(s)
        if m:
            return (('val', int(m.group())), s[m.end():])

        m = re_str.match(s)
        if m:
            return (('val', m.group()[1:-1]), s[m.end():])

        for (name, op) in self.infixes.iteritems():
            if s.startswith(name):
                raise ParseError("bad use of infix operator " + name)

        m = re_var.match(s)
        if m:
            name = m.group()
            if name in self.macros:
                v = self.macros[name]
            else:
                v = ('var',name,0)
            return (v, s[m.end():])

        m = re_popen.match(s)
        if m:
            (x,s) = self.parse_whole(s[m.end():])
            s = s.lstrip()
            m = re_pclose.match(s)
            if not m:
                raise ParseError('unclosed parenthesis?')
            return (x, s[m.end():])

        if re_pclose.match(s):
            raise ParseClose('unexpected close paren: ' + s)

        raise ParseError('could not parse: ' + s)


# ---------- EVALUATOR ----------
class Stuck(LamError): pass
class UnboundVar(Stuck): pass
class AlreadyAValue(Stuck): pass

def isvalue(e):
    typ = e[0]
    return typ in ['lam','val']

def eval(e, macros=None):
    while not isvalue(e):
        e = step(e, macros=macros)
    return e

def nstep(n, e):
    while n:
        e = step(e)
        n -= 1
    return e

def step(e, macros=None):
    if isvalue(e):
        raise AlreadyAValue("can't step a value")

    typ = e[0]
    if typ == 'var':
        typ, name, idx = e
        if macros and name in macros and idx == 0:
            return macros[name]
        raise UnboundVar('unbound variable: ' + name)

    elif typ == 'app':
        typ, fnc, arg = e
        if not isvalue(fnc):
            return (typ, step(fnc, macros), arg)
        elif not isvalue(arg):
            return (typ, fnc, step(arg, macros))
        elif fnc[0] == 'lam':
            ftyp, fvar, fbody = fnc
            return subst(arg, fvar, 0, fbody)
        elif fnc[0] == 'val':
            ftyp, fval = fnc[:2]
            try:
                return fval(arg)
            except TypeError as e:
                raise Stuck(str(e))
        else:
            raise Stuck(
                "value in function position not lambda or embedded value")

    elif typ in ['lam', 'val']:
        raise AlreadyAValue("can't step a value")

    else:
        raise Malformed('unrecognized expression type: %r' % typ)

# substitutes v for x_i in e, avoiding capture
def subst(v, x, i, e):
    typ = e[0]
    if typ == 'var':
        typ, name, idx = e
        if x == name and i == idx:
            return v
        else:
            return e

    elif typ == 'app':
        return (typ, subst(v, x, i, e[1]), subst(v, x, i, e[2]))

    elif typ == 'val':
        return e

    elif typ == 'lam':
        typ, var, body = e
        if x == var: i += 1
        v = lift(var, 0, v) or v
        return (typ, var, subst(v,x,i,body))

    else:
        raise Malformed('unrecognized expression type: %r' % typ)

def lift(x, i, e):
    # Returns None if no lifting was necessary. Helps conserve memory.
    typ = e[0]
    if typ == 'var':
        typ, name, idx = e
        if name == x and idx >= i:
            return (typ, name, idx + 1)
        return None

    elif typ == 'app':
        a, b = lift(x,i,e[1]), lift(x,i,e[2])
        if a or b:
            return (a or e[1], b or e[2])
        return None

    elif typ == 'lam':
        typ, var, body = e
        if x == var: i += 1
        body = lift(x, i, body)
        if body:
            return (typ, var, lift(x, i, body))
        return None

    elif typ == 'val':
        return None

    else:
        raise Malformed('unrecognized expression type: %r' % typ)


# ---------- BUILTINS ----------
def iffnc(c,t,e):
    if c: return t
    else: return e

lam_true = embed(True, 'true')
lam_false = embed(False, 'false')
embed_bool = lambda x: lam_true if x else lam_false

lam_add = embed_func([object, object], (lambda x,y: embed(x+y)), '+', 5, 1)
lam_sub = embed_func([object, object], (lambda x,y: embed(x-y)), '-', 5, 1)
lam_mul = embed_func([object, object], (lambda x,y: embed(x*y)), '*', 4, 1)
lam_div = embed_func([object, object], (lambda x,y: embed(x/y)), '/', 4, 1)

lam_if = embed_func([bool, None, None], iffnc, 'if')

lam_eq  = embed_func([None,None], (lambda x,y: embed_bool(x==y)), '==', 10, 0)
lam_neq = embed_func([None,None], (lambda x,y: embed_bool(x!=y)), '!=', 10, 0)
lam_lt  = embed_func([None,None], (lambda x,y: embed_bool(x<y)) , '<',  10, 0)
lam_leq = embed_func([None,None], (lambda x,y: embed_bool(x<=y)), '<=', 10, 0)
lam_gt  = embed_func([None,None], (lambda x,y: embed_bool(x>y)),  '>',  10, 0)
lam_geq = embed_func([None,None], (lambda x,y: embed_bool(x>=y)), '>=', 10, 0)


# ---------- REPL ----------
class ExitRepl(Exception): pass

class Repl(object):
    builtins = { '+': lam_add, '*': lam_mul,
                 '-': lam_sub, '/': lam_div,
                 'if': lam_if,
                 'true': embed(True, 'true'),
                 'false': embed(False, 'false'),
                 '==': lam_eq, '!=': lam_neq,
                 '<': lam_lt, '<=': lam_leq, '>': lam_gt, '>=': lam_geq
               }

    def __init__(self, parser=None, exit_when_done=False):
        self.globals = {}
        self.builtins = Repl.builtins
        self.macros = dict(self.builtins)
        self.max_steps = 1000
        self.exit_when_done = exit_when_done
        self.last = None

    def repl(self):
        try:
            while True:
                print 'lambda>',
                try:
                    self.handle_line()
                except LamError as e:
                    print 'Error:', e
                except EOFError:
                    self.exit()
        except ExitRepl:
            if self.exit_when_done:
                exit()

    def exit(self):
        raise ExitRepl()

    def handle_line(self):
        line = raw_input().lstrip()
        words = line.split(None, 1)
        if not words: return
        cmd = words[0]
        if words[1:]: rest = words[1].lstrip()
        else: rest = ''

        if cmd == 'step':
            self.do_step(self.rest_or_last(rest, 'step'))

        elif cmd == 'exit':
            self.exit()

        elif cmd == 'eval':
            self.do_eval(self.rest_or_last(rest, 'eval'))

        elif cmd == 'reset':
            print 'Resetting global variables'
            self.global_reset()

        elif cmd == 'globals':
            print "Global variables:"
            for (k,v) in self.globals.iteritems():
                print '  %s = %s' % (k, pretty(v))

        elif cmd == 'builtins':
            print 'Builtins: ' + ', '.join(sorted(self.builtins.keys()))
            # for (k,v) in self.builtins.iteritems():
            #     print '  %s = %s' % (k, pretty(v))

        elif rest.startswith('= '):
            # Setting a global
            # FIXME: should check that cmd is valid var name
            e = self.parse(rest[2:])
            self.last = e
            self.global_set(cmd, self.eval(e))

        else:
            # Default is to eval the expression.
            self.do_eval(line)

    def rest_or_last(self, rest, purpose):
        if rest:
            return self.parse(rest)
        elif self.last:
            return self.last
        else:
            raise LamError("What do you want me to %s?" % purpose)

    def do_eval(self, line):
        expr = self.parse(line)
        self.last = expr
        print pretty(self.eval(expr))

    def do_step(self, expr):
        try:
            e = self.step(expr)
            self.last = e
            print pretty(e)
        except AlreadyAValue:
            print 'Already a value:', pretty(expr)

    def parse(self, s):
        return parse(s, macros=self.macros)

    def eval(self, expr):
        for i in xrange(self.max_steps):
            if isvalue(expr):
                return expr
            expr = self.step(expr)
        raise LamError('evaluation took more than %s steps, aborting' %
                       self.max_steps)

    def step(self, expr):
        return step(expr)

    # managing globals and macros
    def global_set(self, var, val):
        self.globals[var] = val
        self.macros[var]= val

    def global_unset(self, var):
        del self.globals[var]
        del self.macros[var]
        if var in self.builtins:
            self.macros[var] = self.builtins[var]

    def global_reset(self):
        self.globals = {}
        self.macros = dict(self.builtins)

def repl():
    global r
    if not "r" in globals() or not isinstance(r, Repl):
        r = Repl()
    r.repl()

print 'here'
