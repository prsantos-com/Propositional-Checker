This is a modified tautology checker that checks if two propositional
statements are equal in their evaluation.

It comes from the Tautology checker example from section 10.4 of 
Programming in Haskell, Graham Hutton, Cambridge University Press, 2007.


Propositional checker
-----------------

\begin{code}
module Myitautology where

import Char
--import Parsing
import System.IO
import Text.ParserCombinators.Parsec --this uses Parsec2

import qualified Data.Set as Set
import Data.Set (Set) 
\end{code}

First our data type is defined which represents common propositional logic
connectives such as Or, And, Implies, etc.

\begin{code} 
type Var = Char

data Prop                     =  Const Bool
                               |  Var Var
                               |  Not Prop
                               |  And Prop Prop
                               |  Or Prop Prop
                               |  Imply Prop Prop
                               |  Equiv Prop Prop
                               |  Equal Prop Prop
                              deriving(Show, Eq)
\end{code}

Subst will act kind of like a substitution since it doesn't really substitute
variables, but rather is type that identifies what Bools should be used for
what variables.

\begin{code}
type Subst                    =  Assoc Char Bool
\end{code}

Assoc acts lookup table for variables to bools, although this a general 
definition which only requires two different types, that may or may not be
Char and Bool.

\begin{code}

type Assoc k v                =  [(k,v)]
type Rel k v = Set (k,v)
--type Fct k v = Map.Map k v
\end{code}

find will take a variable(k) and table of variables to bools and find the first
bool value for k and return it.

\begin{code}
find                          :: Eq k => k -> Assoc k v -> v
find k t                      =  head [v | (k',v) <- t, k == k']
\end{code}

Now that we have defined a way to associate bool values to variables, we can
now use this in another function that recursively evaluates a proposition of 
type Prop. Using the find function it will find the appropriate bool value for
a variable in a proposition and then evaluate the proposition once it has been
constructed.

\begin{code}
eval                          :: Subst -> Prop -> Bool
eval _ (Const b)              =  b
eval s (Var x)                =  find x s
eval s (Not p)                =  not (eval s p)
eval s (And p q)              =  eval s p && eval s q
eval s (Or p q)               =  eval s p || eval s q
eval s (Imply p q)            =  eval s p <= eval s q
eval s (Equiv p q)            =  eval s (Imply p q) && eval s (Imply q p)
eval s (Equal p q)            =  eval s p == eval s q
\end{code}

We will use 'vars' to construct a list of variables, that are in a proposition.
This function will produce duplicate variables, but that's okay for now,
because we will remove them later.

\begin{code}
vars                          :: Prop -> [Char]
vars (Const _)                =  []
vars (Var x)                  =  [x]
vars (Not p)                  =  vars p
vars (And p q)                =  vars p ++ vars q
vars (Or p q)                 =  vars p ++ vars q
vars (Imply p q)              =  vars p ++ vars q
vars (Equiv p q)              =  vars p ++ vars q
vars (Equal p q)              =  vars p ++ vars q
\end{code}

The 'bools' function creates a complete truth table of all possible True and
False combinations for a given number of variables.

\begin{code}
bools                         :: Int -> [[Bool]]
bools 0                       =  [[]]
bools (n+1)                   =  map (False:) bss ++ map (True:) bss
                                  where bss = bools n
\end{code}

This function filters out all the duplicates of a list, and is used to remove
the duplicate variables from the list that is generated from 'vars'.

\begin{code}
rmdups                        :: Eq a => [a] -> [a]
rmdups []                     =  []
rmdups (x:xs)                 =  x : rmdups (filter (/= x) xs)
\end{code}

The function 'substs' will pair the variables produced from 'vars' with the
list of bools generated from 'bools'.

\begin{code}
substs                        :: Prop -> [Subst]
substs p                      =  map (zip vs) (bools (length vs))
                                  where vs = rmdups (vars p)
\end{code}



\begin{code}
isTaut                        :: Prop -> Bool
isTaut p                      =  and [eval s p | s <- substs p]

-- This function will filter out all the props that don't satisfy the given
-- restrictions

type Rests                      =  [Prop]

cleanSubst                      :: [Subst] -> Prop -> [Subst]
cleanSubst []       p           =  []
cleanSubst (s:subs) p           =  if eval s p then
                                        s:cleanSubst subs p
                                   else
                                        cleanSubst subs p
-- |eval s p = flip eval p s = s `eval` p = (`eval` p) s = (\ s -> eval s p) s|
-- |flip cleanSubst p = filter (flip eval p)|

-- This will purge the substition list of any substitutions that do not satisfy
-- the given restrictions. ie, A /= B
readySubst                      :: [Subst] -> Rests -> [Subst]
readySubst subs  []             =  subs
readySubst subs  (p:ps)         =  readySubst (cleanSubst subs p) ps

-- This will create the one part of the final substitution list
keepSubst                         :: [Subst] -> Set.Set (Char, Bool) -> [(Subst, Subst)]
keepSubst subs set1               
                = [(s, Set.toList set1) | s <- subs, set1 `Set.isSubsetOf` Set.fromList s]

-- This will create the final substitution list. The first arguments should
-- take a larger clean substitution list and a smaller substitution list
-- if the last substitution list is of equal size, then isEquiv should be
-- used instead
finalSubst                      :: [Subst] -> [Subst] -> [(Subst, Subst)]
finalSubst subs1 subs2        
                        =  foldl (++) [] [ keepSubst subs1 (Set.fromList s) | s <- subs2 ] 

-- This function works with two propositions that have the same amount of
-- variables. Boring, I know.
isEquiv                         :: Prop -> Prop -> Rests -> Bool
isEquiv p1 p2 r                 =  if p1 == p2 then
                                        True
                                   else
                                        and [eval s p1 == eval s p2 | s <- subs]
                                          where subs = readySubst (substs p1) r

-- This function works with two propositions that have an unequal amount of
-- variables. The substitution list always has the propositions with more
-- variables p1.
isEquiv'                        :: Prop -> Prop -> [(Subst,Subst)] -> Bool
isEquiv' p1 p2 subs             =  and [eval s1 p1 == eval s2 p2 | (s1,s2) <- subs]


-- Give propMachine two propositions and it's restrictions and it will tell you
-- If they are equivalent
propMachine                     :: Prop -> Prop -> Rests -> Bool
propMachine p1 p2 r             =  if varLp1 > varLp2 then
                                        isEquiv' p1 p2 (finalSubst (cSub1) (substs p2))

                                   else if varLp2 > varLp1 then
                                        isEquiv' p2 p1 (finalSubst (cSub2) (substs p1))
                                   else
                                        isEquiv p1 p2 r
                                        where cSub1 = readySubst (substs p1) r
                                              cSub2 = readySubst (substs p2) r
                                              varLp1 = length (rmdups (vars p1))
                                              varLp2 = length (rmdups (vars p2))
\end{code}

\begin{code}
-- Test propositions
--------------------
p1  :: Prop
p1  =  And (Var 'A') (Not (Var 'A'))

p2  :: Prop
p2  =  Imply (And (Var 'A') (Var 'B')) (Var 'A')

p3  :: Prop
p3  =  Imply (Var 'A') (And (Var 'A') (Var 'B'))

p4  :: Prop
p4  =  Imply (And (Var 'A') (Imply (Var 'A') (Var 'B'))) (Var 'B')

p5  :: Prop
p5  =  Or (Not (Var 'A')) (Var 'A')

p6  :: Prop
p6  =  Equiv (Imply (Var 'A') (Var 'B')) (Imply (Not (Var 'B')) (Not (Var 'A')))

p7  :: Prop
p7  =  Equiv (Not (And (Var 'A') (Var 'B'))) (Or (Not (Var 'A')) (Not(Var 'B')))

p8  :: Prop
p8  =  Imply (Var 'A') (Or (Var 'B') (Var 'C'))

p9  :: Prop
p9  =  Or (Imply (Var 'A') (Var 'B')) (Imply (Var 'A') (Var 'C'))

-- Ladies or Tigers example

p10 :: Prop
p10 =  Equiv (Var 'a') (Var 'd')

p11 :: Prop
p11 =  And (Or (Var 'a') (Var 'b')) (Or (Var 'c') (Var 'd'))

r1 :: Prop
r1 =  Not (Equal (Var 'a') (Var 'c'))

r2 :: Prop
r2 =  Not (Equal (Var 'b') (Var 'd'))

s1 :: Prop
s1 =  And (Var 'a') (Var 'd')

s2 :: Prop
s2 =  p11

s1s2 :: Prop
s1s2 =  Not (Equiv (s1) (s2))

s3 :: Prop
s3 =  And (Var 'b') (Var 'c')
-- Tautology Parser and Checker (this needs to be rewritten using Parsec2)
-------------------------------
{-
isVar                   :: Char -> Bool
isVar c                 =  isAlpha c && c /= 'v'

var                     :: Parser Char
var                     =  satisfy isVar

variable                :: Parser Char
variable                =  lexeme var

props                   :: Parser Prop
props                   =  do j <- junc
                              do string "=>"
                                 p <- props
                                 return (Imply (j) (p))
                                <|> do string "<=>"
                                       p <- props
                                       return (Equiv (j) (p))
                                <|> return j

junc                    :: Parser Prop
junc                    =  do v <- vari
                              do string "&"
                                 j <- junc
                                 return (And (v) (j))
                                <|> do string "v"
                                       j <- junc
                                       return (Or (v) (j))
                                <|> return v

vari                    :: Parser Prop
vari                    =  do string "~"
                              va <- vari
                              return (Not va)
                             <|> do string "("
                                    p <- props
                                    string ")"
                                    return p
                             <|> do v <- variable
                                    return (Var v)
-}
{-
evalprop                :: String -> Prop
evalprop xs             =  case (parse props xs) of
                             [(n,[])]  -> n
                             [(_,out)] -> error ("unused input " ++ out)
                             []        -> error "invalid input"
-}


\end{code}	
