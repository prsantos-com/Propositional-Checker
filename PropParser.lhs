This is my propostional parser using Parsec (parsec2 package)

\begin{code}
module PropParser where

import Text.ParserCombinators.Parsec -- :set -ignore-package parsec-3.1.0
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language (haskellDef)
import Text.ParserCombinators.Parsec.Char

import Myitautology
import Char
\end{code}

\begin{code}


{-
---------- old Expression
isVar                   :: Char -> Bool
isVar c                 =  isAlpha c && c /= 'v'

var                     :: Parser Char
var                     =  satisfy isVar

variable                :: Parser Char
variable                =  T.lexeme var

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
----------
-}





-- The Parser
mainParser = do whiteSpace
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

isVar                   :: Char -> Bool
isVar c                 =  isAlpha c && c /= 'v'

var                     :: Parser Prop
var                     =  fmap Var $ satisfy isVar

evalProp               :: String -> String
evalProp xs            =  case (parse mainParser "" xs) of
                                Left err -> show err
                                Right  p -> show (isTaut p)

-- The lexer
lexer       = T.makeTokenParser haskellDef
lexeme      = T.lexeme

parens      = T.parens lexer
natural     = T.natural lexer
reservedOp  = T.reservedOp lexer
whiteSpace  = T.whiteSpace lexer



\end{code}
