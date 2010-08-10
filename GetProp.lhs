%% \documentclass{article}
%% %include polycode.fmt
%% \begin{document}
\medskip
The final section attempts to explain how exactly all the previously defined
functions work with the Happstack web framework, as well as the use of the HTML
generator Blaze-Html.
\section*{The Propositional Checker Website --- GetProp}
This interactive website uses a modified version of the RqDataUpload.hs source 
from the Happstack Crash Course at happstack.com. Additional help was received
from the people at the |happstack| IRC channel. In the beginning the important
modules to import are of course |Happstack.Server| and |Blaze|. |Monad| is also
imported to allow for simplified request matching.
\begin{code}
{-# LANGUAGE OverloadedStrings #-}
import Control.Monad                      (msum)
import Happstack.Server                   (Response, ServerPart, 
                                          Method(GET, POST), methodM
                                          , defaultBodyPolicy, dir, getDataFn
                                          , look, lookInput, fileServe, nullDir
                                          , notFound
                                          , nullConf, ok, simpleHTTP, toResponse
                                          , seeOther)
import Text.Blaze                         as B
import Text.Blaze.Html4.Strict            as B hiding (map)
import Text.Blaze.Html4.Strict.Attributes as B hiding (dir, title) 

import PropChecker
import PropParser as P
\end{code}
The advice given is that two pages need to be generated. In Happstack,
a |ServerPart Response| is considered a page. One page will setup the form to 
collect a proposition from the student and post it, and the next page will parse
that information and generate a |Response| page, which will display whether the
proposition is correct or incorrect, and provide feedback if the proposition is
malformed or incorrect. To begin, |GetProp| is executed, the simpleHTTP server
takes |propcheck|, which is a route filter that matches a request to a response.
\begin{code}
main :: IO ()
main = simpleHTTP nullConf $ propcheck
\end{code}
As explained earlier, |propcheck| is the route filter which matches requests
with the correct response. For 'dir "feedback"' has methodM POST attached to it
in order match on the specific HTTP request, and if it does match, then produce 
the page, otherwise a custom error page, |errorPage| will be generated. 
This way, anyone trying to make a request on 'feedback' will get the |errorPage|.
This is done with a nested msum (or filter), which allows for a future decision
to remove the |errorPage| or add more possibilities simply by adding or 
subtracting elements from the nested msum. The next match, dir "static" is used
with |fileServe| to serve up any files that are used, with the last argument
stating where to look for the file, in this the current directory. |nullDir| 
will check if the path is non-empty, and if it is, the filter will move onto the 
next item, which is notExist, custom 404 message. This kind of customization can 
add a sense of user-friendliness.
\begin{code}
propcheck :: ServerPart Response
propcheck = 
    msum [ dir "feedback" $ msum [ methodM POST >> feedback
                                 , errorPage
                                 ]
         , dir "static" $ fileServe [] "." 
         , nullDir >> propForm
         , notExist
         ]
\end{code}
This is the form page that will collect the user's input and post it as
|user_prop| if the user clicks on the 'Check this proposition' button. It also
acts as the default page. The blaze-html module allows the use of the same tags
that would be normally used in an explicit html file.
\begin{code}
propForm :: ServerPart Response
propForm = ok $ toResponse $
    html $ do
      B.head $ do
        title "Propositional Equivalance Checker"
      B.h1 $ do
        text "Peter's Propositional Equivalence Checker"
      B.body $ do
        p (string $ question1)
        p "Where:"
        ul $ li $ text "a = Room 1 has a lady"
        ul $ li $ text "b = Room 1 has a tiger"
        ul $ li $ text "c = Room 2 has a lady"
        ul $ li $ text "d = Room 2 haa a tiger"
        p "Given:"
        ul $ li $ text "a is not equivalent to b"
        ul $ li $ text "c is not equivalent to d"
      B.div $ do
        
      B.div $ do
        p (string $ instructions)
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/feedback" $ do
             input ! type_ "text" ! name "user_prop" ! size "40" ! maxlength "40"
             input ! type_ "submit" ! name "check_prop" ! value "Check this proposition"
             input ! type_ "reset" ! name "clear_prop" ! value "Clear"

instructions :: String
instructions =  "Enter a proposition that describes this situation. "

question1 :: String
question1 =  "[...] the king explained to the prisoner that each of the two "
          ++ "rooms contained either a lady or a tiger, but it could be that "
          ++ "there were tigers in both rooms, or ladies in both rooms, or "
          ++ "then again, maybe one room contained a lady and the other room "
          ++ "a tiger."       
\end{code}
For the |feedback| page, the |getDataFn| is used to get the posted value
contained in |user_prop|. The first argument of this function also sets the
allow upload file size, but in this case, it doesn't matter what the values are.
The function |mkBody| will post an error message if there is anything wrong with
the value that is posted that is not a parsing issue.  Once it is determined to
be a correct value, in this a case a |String|, it is sent to the |PropParser|
function |evalProp| to be evaluated. Based on it's evaluation, an appropriate
part of a page will be generated via the |isEquivalent| function, and put into 
the body tag of |feedback|.
\begin{code}
feedback :: ServerPart Response
feedback = 
   do r <- getDataFn (defaultBodyPolicy "/tmp/" 1000 1000 1000) $ look "user_prop"
      ok $ toResponse $
         html $ do
           B.head $ do
             title "Prop Feedback"
           B.h2 $ do
             text "Feedback on given Proposition    "           
             img ! src "/static/lambda.gif" ! alt "lambda" ! width "20" ! height "20"
           B.body $ do
             mkBody r
    where
      mkBody (Left errs) =
          do p $ "The following error occurred:"
             mapM_ (p . string) errs
      mkBody (Right theprop) = do
                B.h3 $ do
                  text "Analysis"
                isEquivalent (P.evalProp theprop prop1 rests1) theprop

isEquivalent               :: String -> String -> Html b
isEquivalent "True"  prop  =  p (string $ "Your proposition '" ++ prop ++ 
                                "' correctly describes this situation.")
isEquivalent "False" prop  =  do
                                p (string $ "Your proposition '" ++ prop ++
                                 "' incorrectly describes this situation.")
                                B.h4 $ text "Here's a tip: "
                                p (string $ "When " ++ evalDisagree prop prop1 rests1 ++
                                 "Carefully look over the " ++
                                 "information that is being given to you and try again.")
isEquivalent error   prop  =  do
                                p (string $ ("'" ++ prop ++ "' is not a correctly" ++
                                  " written proposition."))
                                B.h4 $ text "Check "
                                p (string $ betterError error)

betterError             :: String -> String
betterError err         =  drop 8 (filter (/= ')') err)
\end{code} 
The host of the website can enter their proposition and restrictions for each
question that is presented.
\begin{code}
rests1 :: Rests
rests1 =  [ Not (Equiv (Var 'a') (Var 'c'))
          , Not (Equiv (Var 'b') (Var 'd'))
          ]

prop1 :: String
prop1 =  "(a v b) & (c v d)"
\end{code}
These are the custom error pages, one is for when a user tries to go to the
feedback page directly, and the other is when they enter a non-existent url.
It can clearly be shown that each page must first set its html response code, as
can be seen for the first error page where it is just the standard |ok| and 
with the second page it is the proper |notFound| response code.
\begin{code}
errorPage :: ServerPart Response
errorPage = ok $ toResponse $
    html $ do
      B.head $ do
        title "Error Page"
      B.h1 $ do
        text "Oops!"
      B.body $ do
        p $ "It seems you tried to check your feedback without submitting a proposition."
      B.div $ do
        p $ ""

notExist :: ServerPart Response
notExist = notFound $ toResponse $
    html $ do
      B.head $ do
        title "Error Page"
      B.h1 $ do
        text "Sorry!"
      B.body $ do
        p $ "This page doesn't exist, maybe you can ask for it to be in the next version."
      B.div $ do
        p $ ""
\end{code}
\section*{Conclusion}
This was an enjoyable project, even with all the obstacles encountered, and
would have been much smoother with prior knowledge of how web services work,
specifically the concepts of server requests and responses as well as the GET
and POST concepts. More tutorials, or tutorials of a specific application such
as this one would have helped in the learning process, but since this is
bleeding edge technology, it is understandable that this wasn't the case. Most
of the support in dealing with Happstack came from the |happs| IRC channel.
Which proved to be extremely useful especially during the initial setup of the
Happstack framework, as a blur of packages had to be installed due to dependencies
and even a reinstallation of Happstack due to faulty previous installations of
GHC packages. Another obstacle of working with Happstack was not having a
complete solid understanding of Haskell, which made for a more difficult time in
deciphering the different types that functions were.  Having said that, the
code presented does makes sense in this application. Blaze-html also seems very
promising, by the looks of it, a person could most likely take any non-complex
or possibly complex website and generate it's blaze-html equivalent. The great 
part about this project was discovering the power of functional programming 
languages, specifically Haskell. Seeing real applications and how they can be 
developed on the web and off the web is powerful in demonstrating to students 
that this language or rather paradigm should not be overlooked when considering 
application development simply because it is different and not familiar.  The 
support for the |Haskell| language seems to very lively, especially on the 
|haskell| IRC channel. In the future it would be nice to try use Happstack with
user accounts and a slightly more complex website.  Also, in Haskell functions
it would be nice to tie in the application of verification techniques to
demonstrate how they would be encountered or used in the real world, even if it
is somewhat trivial or unnecessary to do so in this respect to this application.
As this project has demonstrated, examples are powerful.
%% \end{document}
