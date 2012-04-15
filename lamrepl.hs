{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
    MultiParamTypeClasses, FunctionalDependencies, PatternGuards,
    FlexibleContexts, Rank2Types, ImpredicativeTypes
  #-}
module LamRepl where

import Data.Char (toUpper)
import Data.List (find, intercalate)
import Data.Maybe (mapMaybe, isJust, fromJust, fromMaybe)
import Data.Set (Set)
import qualified Data.Set as S

import Control.Applicative

import Control.Monad
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Writer


-- Miscellaneous utility
setMapMaybe :: (Ord a, Ord b) => (a -> Maybe b) -> Set a -> Set b
setMapMaybe f s = S.map fromJust $ S.filter isJust $ S.map f s

mapFst f (x,y) = (f x, y)

parenShows :: Show a => a -> ShowS
parenShows e r = "(" ++ showsPrec 0 e (")" ++ r)


-- Terms
type Id = String
type Ix = Int
type Var = (Id,Ix)

data Exp b = Lam Id (Exp b)
           | App (Exp b) (Exp b)
           | Var Var
           | Base b

-- Function and operator metadata
data Assoc = LeftAssoc | RightAssoc | NonAssoc
type Prec = Int            -- 0-11, higher is tighter. 10 is application.
type Fixity = (Assoc, Prec)
type Arity = Int                -- 0 indicates non-function.
type IsInfix = Bool

-- Errors
data Err b = Fail String
           | AlreadyValue
           | UnboundVar Var
           | Uncallable (Exp b)
           | TypeError String
             deriving Show

instance Error (Err b) where
    strMsg s = Fail s


-- Evaluation monad
class (MonadWriter String m) => EvalMonad b m | m -> b where
    evalPrint :: String -> m ()
    raise :: Err b -> m a
    handle :: m a -> (Err b -> m a) -> m a

type EvalM b = ErrorT (Err b) (Writer String)

runEvalM :: EvalM b a -> (Either (Err b) a, String)
runEvalM e = runWriter $ runErrorT e

instance EvalMonad b (EvalM b) where
    evalPrint = tell
    raise = throwError
    handle = catchError

-- What is needed for a base type.
class Show b => BaseType b where
    call :: EvalMonad b m => b -> [Exp b] -> m (Exp b)
    arity :: b -> Arity
    fixity :: b -> Maybe Fixity
    -- TODO: read

instance BaseType b => Show (Exp b) where
    -- precedence is from 0 to 11, higher is tigher. application has precedence
    -- 10. we inherit these conventions from haskell, because they happen to
    -- work for us.

    -- TODO: infix operators.
    showsPrec _ (Var (x,0)) r = x ++ r
    showsPrec d (Var (x,i)) r = x ++ "_" ++ showsPrec d i r
    showsPrec d e@(App f a) r
        | d > 10 = parenShows e r
        | otherwise = showsPrec 10 f (" " ++ showsPrec 11 a r)
    showsPrec d e@(Lam _ _) r
        | d > 0 = "(" ++ showsPrec 0 e (")" ++ r)
        | otherwise = "\\" ++ intercalate " " ids ++ ". " ++ showsPrec 0 body r
        where (ids, body) = pullLams e
              pullLams (Lam i b) = mapFst (i:) (pullLams b)
              pullLams e = ([],e)
    showsPrec d (Base b) r
        | Just _ <- fixity b = parenShows b r
        | otherwise = showsPrec d b r

-- free variable finder
freeVars :: Exp b -> Set Var
freeVars (Base _) = S.empty
freeVars (Var v) = S.singleton v
freeVars (App x y) = S.union (freeVars x) (freeVars y)
freeVars (Lam name body) = setMapMaybe drop (freeVars body)
    where drop x@(v,i) | v == name = if i == 0 then Nothing else Just (v,i-1)
                       | otherwise = Just x

freeIds :: Exp b -> Set Id
freeIds = S.map (\(id,_) -> id) . freeVars

-- finds an infinite list of var names not in input list
uniqVarsExcluding :: Set Id -> [Id]
uniqVarsExcluding fvs = filter (\x -> not (S.member x fvs)) uniqVars
    where
      alpha = "abcdefghijklmnopqrstuvwxyz"
      alphas = map (:[]) (alpha ++ map toUpper alpha)
      nats = iterate (+1) 0
      uniqVars = alphas ++ concatMap (\i -> map (++ show i) alphas) nats

uniqVars :: [Exp b] -> [Id]
uniqVars = uniqVarsExcluding . S.unions . map freeIds

-- Substitution, evaluation, etc.
isValue :: BaseType b => Exp b -> Bool
isValue (Lam _ _) = True
isValue (Base _) = True
isValue _ = False

-- sharing-optimized version of subst. more strict than a naive version, but
-- whatever. Returns Nothing if the term didn't change.
substM :: Exp b -> Var -> Exp b -> Maybe (Exp b)
substM _ _ (Base _) = Nothing
substM a (x,i) (Var (ex,ei)) | x /= ex = Nothing
                             | i < ei = Just (Var (ex, ei-1))
                             | i > ei = Nothing
                             | otherwise = Just a
substM a v@(x,i) (Lam y e) = Lam y <$> substM a (x,i') e
    where i' | x == y = i+1
             | otherwise = i
substM a v (App f g) = case (substM a v f, substM a v g) of
                         (Nothing, Nothing) -> Nothing
                         (f',g') -> Just $ App (fromMaybe f f') (fromMaybe g g')

subst :: Exp b -> Var -> Exp b -> Exp b
subst a v e = fromMaybe e (substM a v e)

data StepRes b = IsValue
               | Step (Exp b)
               -- in (Call b as),
               -- 1. invariant: `length as < arity b'
               -- 2. `as' is list of args in reverse order
               | Call b [Exp b]

stepRaw :: BaseType b => Exp b -> EvalM b (StepRes b)
stepRaw x@(Lam _ _) = return IsValue
stepRaw (Base b) = return $ if 0 == arity b then IsValue else Call b []
stepRaw (Var v) = raise (UnboundVar v)
stepRaw (App f a) =
    do fs <- stepRaw f
       case fs of
         IsValue | isValue a ->
                     case f of
                       Lam name body -> return $ Step $ subst a (name,0) body
                       _ -> raise (Uncallable f)
                 -- this isn't strictly necessary, but appeases the
                 -- exhaustiveness checker.
                 | otherwise -> Step . App f <$> step a
         Step f' -> return $ Step $ App f' a
         _ | not (isValue a) -> Step . App f <$> step a
         Call b as -> case compare (arity b) (1 + length as) of
                        EQ -> Step <$> call b (reverse (a:as))
                        GT -> return $ Call b (a:as)
                        LT -> error "invariant violation"

step :: BaseType b => Exp b -> EvalM b (Exp b)
step x = do xs <- stepRaw x
            case xs of
              IsValue -> raise AlreadyValue
              Step x' -> return x'
              Call b [] -> raise AlreadyValue
              Call b as -> let ids = (take (arity b - length as) (uniqVars as))
                               vars = map (\x -> Var (x,0)) ids
                               body = foldl App (Base b) (reverse as ++ vars)
                           in return $ foldr Lam body ids

eval :: BaseType b => Exp b -> EvalM b (Exp b)
eval x = do r <- handle (Just <$> step x) handler
            case r of Just x' -> eval x'
                      Nothing -> return x
    where handler AlreadyValue = return Nothing
          handler e = raise e


-- Useful base type
data Op = Add | Sub | Mul | Div
        | Join                  -- string catenation
        | Print

type OpInfo = (String, Arity, Maybe Fixity,
               (forall m. EvalMonad Base m => [Exp Base] -> m (Exp Base)))

opInfo :: Op -> OpInfo
opInfo Add = arith "+" LeftAssoc 6 (+)
opInfo Sub = arith "-" LeftAssoc 6 (-)
opInfo Mul = arith "*" LeftAssoc 7 (*)
opInfo Div = arith "/" LeftAssoc 7 (div)
opInfo Join = strOp "@" RightAssoc 5 (++)
opInfo Print = ("print", 1, Nothing, (\[x] -> do tell (show x ++ "\n")
                                                 return x))

opName o = name where (name, _, _, _) = opInfo o
opArity o = arity where (_, arity, _, _) = opInfo o
opFixity o = fixity where (_, _, fixity, _) = opInfo o
opFunc o = func where (_, _, _, func) = opInfo o

arith :: String -> Assoc -> Prec -> (Int -> Int -> Int) -> OpInfo
arith name ass prec fn = baseOp name ass prec fn "int" Int getInt
    where getInt (Int x) = Just x
          getInt _ = Nothing

strOp name ass prec fn = baseOp name ass prec fn "string" String getString
    where getString (String x) = Just x
          getString _ = Nothing

baseOp :: String -> Assoc -> Prec -> (a -> a -> b) ->
          String -> (b -> Base) -> (Base -> Maybe a) -> OpInfo
baseOp name ass prec fn typename inj proj = (name, 2, Just (ass,prec), func)
    where func [Base x, Base y]
              | Just x' <- proj x,
                Just y' <- proj y = return $ Base $ inj $ fn x' y'
          func _ = raise $ TypeError $
                   "operator " ++ name ++ " expects " ++ typename ++ "s"

instance Show Op where show = opName

data Base = Int Int
          | String String
          | Op Op

instance Show Base where
    show (Int i) = show i
    show (String s) = show s
    show (Op o) = show o

instance BaseType Base where
    fixity (Op o) = opFixity o
    fixity _ = Nothing
    arity (Op o) = opArity o
    arity _ = 0
    call (Op o) es | opArity o == length es = opFunc o es
                   | otherwise = error "arity mismatch"
    call _ _ = error "impossible"
