\documentclass{article}
%include polycode.fmt
%include WKlhs.sty
\setlength{\textwidth}{170mm}
\setlength{\textheight}{240mm}
\setlength{\hoffset}{-27mm}
\setlength{\voffset}{-20mm}
\parskip=4pt
\parindent=0pt
\begin{document}
\title{CS 4Z03 - Functional Programming, in Application to 
Interactive Web Interfaces for Discrete Mathematics Education}
\author{Peter Santos}
\date{\today}
\maketitle
\begin{abstract}
This project attempts to address the problem of helping students learn to
address problems in natural language using propositional logic. The solution is
implemented via an interactive web interface that is developed strictly using
the functional programming language Haskell and its relatively new web framework 
Happstack. The implementation was relatively successful and demonstrates the
potential power of Haskell and Happstack in providing educational tools via an
interactive web interface. 
\end{abstract}


\section*{Introduction}
In developing a web interface, Happstack will be used for the web framework, and
Blaze-html will be used to generate the html for the web pages.  In order to
allow for the comparison and evaluation of two logical propositions, three major
modules will be needed to make a complete web interface. These three major
modules are |PropChecker|, |PropParser|, and |GetProp|, as such the document
will be split into three sections describing these modules. |PropChecker| will
take care of the comparing two logical propositions, |PropParser| will take
care of converting a given String from a user to a propositional statement, and
|GetProp| will take care of generating the web interface that will receive
propositions from the user and generate custom feedback. The complete web interface will
only demonstrate one question that a user can answer at the moment, but it
should be noted that generating more questions would simply be a matter of
either adding more pages using the exact same layout or adding additional
questions with input boxes on the same page.  The mean idea is to show that it
can be done, and later it can be seen scaling the site with more questions should not
be too difficult of a task, once everything is in place.

\medskip
This first section will describe and explain how the propositional checker
works and lay the foundation for how the web interface will generate its
results.
\section*{The Propositional Checker --- |PropChecker|}
This is a modified tautology checker that checks if two propositional
statements are equal in their evaluation.  It comes from the Tautology checker 
example in section 10.4 of \emph{Programming in Haskell}, by Graham Hutton. This
propositional checker no longer evaluates if a proposition a tautology, though
two extra lines of code could enable this feature.
\\\\
To begin, |Data.Set| is imported to allow for a more intuitive way of
manipulating the lists that will be used in determining whether a proposition
is equivalent to another, which will be discussed later.
\begin{code}
module PropChecker where

import qualified Data.Set as Set
import Data.Set (Set) 
\end{code}
A new data type is now defined which represents common propositional
logic connectives such as |Or|, |And|, |Imply|, etc.
\begin{code} 
type Var = Char

data Prop                     =  Const Bool
                               |  Var Var
                               |  Not Prop
                               |  And Prop Prop
                               |  Or Prop Prop
                               |  Imply Prop Prop
                               |  Equiv Prop Prop
                              deriving(Show, Eq)

\end{code}
|Subst| will act kind of like a substitution since it doesn't really 
substitute variables, but rather is a type that identifies what Bools should be 
used for what variables.
\begin{code}
type Subst                    =  Assoc Char Bool
\end{code}
|Assoc| acts as a lookup table for variables to Bools, although this a 
general definition which only requires two different types that may or may not 
be |Char| and |Bool|.
\begin{code}
type Assoc k v                =  [(k,v)]
--type Rel k v = Set (k,v)
--type Fct k v = Map.Map k v
\end{code}
|find| will take a variable(k) and table(t) of variables to bools and find
the first bool value(v) for k and return it.
\begin{code}
find                          :: Eq k => k -> Assoc k v -> v
find k t                      =  head [v | (k',v) <- t, k == k']
\end{code}
Now that we have defined a way to associate bool values to variables, we can 
use this in another function that recursively evaluates a proposition of 
type |Prop|. Using the |find| function it will find the appropriate Bool value 
for a variable in a proposition and then evaluate the proposition once it has 
been constructed.
\begin{code}
eval                          :: Subst -> Prop -> Bool
eval _ (Const b)              =  b
eval s (Var x)                =  find x s
eval s (Not p)                =  not (eval s p)
eval s (And p q)              =  eval s p && eval s q
eval s (Or p q)               =  eval s p || eval s q
eval s (Imply p q)            =  eval s p <= eval s q
eval s (Equiv p q)            =  eval s (Imply p q) && eval s (Imply q p)
\end{code}
We will use |vars| to construct a list of variables, that are in a proposition.
This function will produce duplicate variables, but that's okay for now,
because they will be removed later.
\begin{code}
vars                          :: Prop -> [Char]
vars (Const _)                =  []
vars (Var x)                  =  [x]
vars (Not p)                  =  vars p
vars (And p q)                =  vars p ++ vars q
vars (Or p q)                 =  vars p ++ vars q
vars (Imply p q)              =  vars p ++ vars q
vars (Equiv p q)              =  vars p ++ vars q
\end{code}
The |bools| function creates a complete truth table of all possible True and
False combinations for a given number of variables.
\begin{code}
bools                         :: Int -> [[Bool]]
bools 0                       =  [[]]
bools (n+1)                   =  map (False:) bss ++ map (True:) bss
                                  where bss = bools n
\end{code}
This function filters out all the duplicates of a list, and is used to remove
the duplicate variables from the list that is generated from |vars|.
\begin{code}
rmdups                        :: Eq a => [a] -> [a]
rmdups []                     =  []
rmdups (x:xs)                 =  x : rmdups (filter (/= x) xs)
\end{code}
The function |substs| will pair the variables produced from |vars| with the
list of bools generated from |bools|, producing a list of 'substitution' tables.
\begin{code}
substs                        :: Prop -> [Subst]
substs p                      =  map (zip vs) (bools (length vs))
                                  where vs = rmdups (vars p)
\end{code}
The type |Rests| is meant to represent a list of propositions that another
proposition must follow in order to be considered correct.
\begin{code}
type Rests                      =  [Prop]
\end{code}
The function |cleanSubst| will take a |Subst| list and only keep the instances
where |Subst| evaluates to true for the given |Prop|.
\begin{code}
cleanSubst                     :: [Subst] -> Prop -> [Subst]
cleanSubst subs p               = filter (flip eval p) subs
\end{code}
|readySubst| will function as |cleanSubst|, but for multiple restrictions.
\begin{code}
readySubst                      :: [Subst] -> Rests -> [Subst]
readySubst subs  []             =  subs
readySubst subs  (p:ps)         =  readySubst (cleanSubst subs p) ps
\end{code}
Now that a function that can produce a proper substitution list for a
proposition is defined, another function that pairs two substitution lists
together needs to be defined. The |keepSubst| function will take a |Subst| list
and only keep the subsets of the |Subst| list that is provided. 
\begin{code}
keepSubst           :: [Subst] -> Set.Set (Char, Bool) -> [(Subst, Subst)]
keepSubst subs set1 =  [(s, Set.toList set1) | s <- subs, set1 `Set.isSubsetOf` Set.fromList s]
\end{code}
|finalSubst| will create the final substitution list. The first arguments should
take a larger 'proper' substitution list and a smaller substitution list.
If the substitutions are of equal size, then isEquiv should be used instead
\begin{code}
finalSubst             :: [Subst] -> [Subst] -> [(Subst, Subst)]
finalSubst subs1 subs2 =  foldl (++) [] [ keepSubst subs1 (Set.fromList s) | s <- subs2 ] 
\end{code}
The function |isEquiv| works with two propositions that have the same amount of
variables.
\begin{code}
isEquiv                         :: Prop -> Prop -> Rests -> Bool
isEquiv p1 p2 r                 =  if p1 == p2 then
                                        True
                                   else
                                        and [eval s p1 == eval s p2 | s <- subs]
                                          where subs = readySubst (substs p1) r
\end{code}
This function works with two propositions that have an unequal amount of
variables. The first proposition is matched with the first |Subst|, which always
has more variables then the second proposition.
\begin{code}
isEquiv'                        :: Prop -> Prop -> [(Subst,Subst)] -> Bool
isEquiv' p1 p2 subs             =  and [eval s1 p1 == eval s2 p2 | (s1,s2) <- subs]
\end{code}
|propMachine| is takes two propositions and it's restrictions and determines if
they are equivalent.  This setup will make it easier to use later on in the
web interface.
\begin{code}
propMachine             :: Prop -> Prop -> Rests -> Bool
propMachine p1 p2 r     =  if varLp1 > varLp2 then
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
The next few functions will deal with producing a helpful custom error message
to the user. Arguably, this functions could be put in |PropParser| instead of
here, but since these functions are of a comparing nature, it is felt that its
place here would be more appropriate. The first function is needs no explanation.
\begin{code}
safeHead (h:_) =  Just h 
safeHead _     =  Nothing
\end{code}
|fstFalse| takes a possible |Subst| tuple and removes the duplicate entries in
order to be used for further processing.
\begin{code}
fstFalse                 :: Maybe (Subst, Subst) -> Maybe Subst
fstFalse subPair         =  case subPair of
                                Just (s1, s2) -> Just (rmdups (s1 ++ s2))
                                Nothing       -> Nothing 
\end{code}
This function produces the first substitution group in which the two
propositions disagree.
\begin{code}
fstFalsePair         :: Prop -> Prop -> [(Subst, Subst)] -> Maybe Subst
fstFalsePair p1 p2 s =  case (safeHead (takeWhile (\(s1,s2) -> eval s1 p1 /= eval s2 p2) s)) of
                                Just subPair -> fstFalse (Just subPair)
                                Nothing      -> fstFalse Nothing
\end{code}
Once a single substitution list is generated, |disagreeM'| will produce a
custom error message describing what substitution instance causes their
proposition to be incorrect.
\begin{code}
disagreeM'               :: Subst -> String
disagreeM' ((v, b):[])   =  v:" = " ++ (show b) ++ ", your proposition doesn't " ++
                            "correctly describe the situation. "
disagreeM' ((v, b):subs) =  v:" = " ++ (show b) ++ ", " ++ disagreeM' subs
\end{code}
If disagreeM receives |Nothing| then we can deduce that a given proposition
violated the restrictions, since it did not produce a substitution.
\begin{code}
disagreeM               :: Maybe Subst -> String
disagreeM (Just s)      =  disagreeM' s
disagreeM Nothing       =  "your proposition is evaluated, it violates the given " ++
                           "restrictions. "
\end{code}
Finally, |disagree| allows for the generation of a proper error message to be
easily implemented in the web interface, using the previously defined functions.
\begin{code}
disagree         :: Prop -> Prop -> Rests -> String
disagree p1 p2 r =  if varLp1 > varLp2 then
                        disagreeM (fstFalsePair p1 p2 (finalSubst (cSub1) (substs p2)))
                    else if varLp2 > varLp1 then
                        disagreeM (fstFalsePair p2 p1 (finalSubst (cSub2) (substs p1)))
                    else
                        disagreeM (fstFalsePair p1 p2 (finalSubst cSub1 cSub2))
                                where cSub1 = readySubst (substs p1) r
                                      cSub2 = readySubst (substs p2) r
                                      varLp1 = length (rmdups (vars p1))
                                      varLp2 = length (rmdups (vars p2))
\end{code}



%include ../PropParser.lhs
%include ../GetProp.lhs
\end{document}	
