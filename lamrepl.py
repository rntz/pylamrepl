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
# - ("val", v)
#   for an embedded value. any python value will do. Calling an embedded value
#   in the lambda calculus will, unsurprisingly, call it in Python. Note that
#   this means it had better be unary; if you want multiarg embedded functions
#   you must curry manually.

# ---------- UTILITY ----------
def embed(x): return ('val', x)

class LamError(Exception): pass
class Malformed(LamError): pass


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
re_int = re.compile(r'[0-9]+')
re_str = re.compile(r'"([^"\\]*)"')

def parse(s, macros=None):
    p = Parser(macros)
    return p.parse(s)

class Parser(object):
    def __init__(self, macros=None):
        self.macros = macros or {}

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

        return self.parse_app(s)

    def parse_app(self, s):
        res, s = self.parse_one(s)
        while True:
            try:
                (arg, snew) = self.parse_one(s)
            except ParseEnd:
                break
            else:
                res = ('app', res, arg)
                s = snew
        return res, s

    def parse_one(self, s):
        s = s.lstrip()
        if not s: raise ParseEmpty('unexpected end of input')

        m = re_var.match(s)
        if m:
            name = m.group()
            if name in self.macros:
                v = self.macros[name]
            else:
                v = ('var',name,0)
                return (v, s[m.end():])

        m = re_int.match(s)
        if m:
            return (('val', int(m.group())), s[m.end():])

        m = re_str.match(s)
        if m:
            return (('val', m.group(1)), s[m.end():])

        m = re_popen.match(s)
        if m:
            (x,s) = self.parse_whole(s[m.end():])
            s = s.lstrip()
            m = re_pclose.match(s)
            if not m:
                raise ParseError('unclosed parenthesis?')
            return (x, s[m.end():])

        if re_pclose.match(s):
            raise ParseClose('unexpect close paren: ' + s)

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
            ftyp, fval = fnc
            try:
                return fval(arg)
            except TypeError:
                raise Stuck('tried to call non-function?')
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
        v = lift(var, 0, v)
        return (typ, var, subst(v,x,i,body))

    else:
        raise Malformed('unrecognized expression type: %r' % typ)

def lift(x, i, e):
    typ = e[0]
    if typ == 'var':
        typ, name, idx = e
        if name == x and idx >= i:
            return (typ, name, idx + 1)
        return e

    elif typ == 'app':
        return (typ, lift(x,i,e[1]), lift(x,i,e[2]))

    elif typ == 'lam':
        typ, var, body = e
        if x == var: i += 1
        return (typ, var, lift(x, i, body))

    elif typ == 'val':
        return e

    else:
        raise Malformed('unrecognized expression type: %r' % typ)


# ---------- REPL ----------
class ExitRepl(Exception): pass

class Repl(object):
    def __init__(self, exit_when_done=False):
        self.globals = {}
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
            self.globals = {}

        elif cmd == 'globals':
            print "Global variables:"
            for (k,v) in self.globals.iteritems():
                print '  %s = %s' % (k, pretty(v))

        elif rest.startswith('= '):
            # Setting a global
            e = self.parse(rest[2:])
            self.last = e
            self.globals[cmd] = self.eval(e)

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
        return parse(s)

    def eval(self, expr):
        for i in xrange(self.max_steps):
            if isvalue(expr): break
            expr = self.step(expr)
        return expr

    def step(self, expr):
        return step(expr, macros = self.globals)

def repl():
    global r
    if not isinstance(r, Repl):
        r = Repl()
    r.repl()

print 'here'
