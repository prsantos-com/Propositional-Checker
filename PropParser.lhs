%% \documentclass{article}
%% %include polycode.fmt
%% \begin{document}
\medskip
The next section will describe the parser that is used to convert strings
to propositions and evaluate them with given restrictions if they are provided.
\section*{The Propositional Parser --- PropParser}
This propositional parser is built using |Parsec|, more specifically
the parsec2 package, which is meant to be easier to use.
\begin{code}
module PropParser where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language (haskellDef)
import Text.ParserCombinators.Parsec.Char

import PropChecker
import Char
\end{code}
First we define |var| to correctly generate Prop values.
\begin{code}
isVar                   :: Char -> Bool
isVar c                 =  isAlpha c && c /= 'v'

var                     :: Parser Prop
var                     =  fmap Var $ satisfy isVar
\end{code}
Next, we have the main parser which is made using |Expr|, a module that is
well suited for this purpose, allowing for custom error messages as well as a
clean of operators and associativity.
\begin{code}
mainParser = do 
        whiteSpace
        e <- expr
        eof
        return e

expr    = buildExpressionParser table term
        <?> "expression"

term0    =  parens expr
        <|> var
        <?> "simple proposition"

term     = do
        t <- term0
        whiteSpace
        return t

table   :: OperatorTable Char () Prop
table   = [ [prefix "~" Not ]
          , [binary "&" And AssocLeft, binary "v" Or AssocLeft ]
          , [binary "=>" Imply AssocLeft, binary "<=>" Equiv AssocNone ]
          ]

binary  name fun assoc = Infix (do{ reservedOp name; whiteSpace; return fun }) assoc
prefix  name fun       = Prefix (do{ reservedOp name; whiteSpace; return fun })
postfix name fun       = Postfix (do{ reservedOp name; whiteSpace; return fun })
\end{code}
Next, we have the lexer.
\begin{code}
lexer       = T.makeTokenParser haskellDef
lexeme      = T.lexeme

parens      = T.parens lexer
natural     = T.natural lexer
reservedOp  = T.reservedOp lexer
whiteSpace  = T.whiteSpace lexer
\end{code}
This function will be used to in the web interface to collect a user's
answer, parse it into a proposition and then compare it to another proposition
that will be supplied by the host of the site. Restrictions will need to be
supplied in the explicit |Prop| format.
\begin{code}
evalProp                :: String -> String -> Rests -> String
evalProp x1 x2 rs       =  case (parse mainParser "" x1) of
                                Left err1 -> show err1
                                Right  p1 -> case (parse mainParser "" x2) of
                                                Left err2 -> show err2
                                                Right  p2 -> show (propMachine p1 p2 rs)
\end{code}
This function will be used when two propositions are not equivalent. It will
generate the correct error message. In this case, the user either violated
the restrictions or input a proposition that was not equivalent. It worth noting
that improperly formatted input will be caught immediately at the web interface
in order to produce a correct error message.
\begin{code}
evalDisagree            :: String -> String -> Rests -> String
evalDisagree x1 x2 rs   =  case (parse mainParser "" x1) of
                                Left err1 -> show err1
                                Right p1 -> case (parse mainParser "" x2) of
                                                Left err2 -> show err2
                                                Right  p2 -> disagree p1 p2 rs


\end{code}
%\end{document}
