My first attempt at producing something remotely close to my Propositional
Checker website. A modified version of the RqDataUpload.hs source from the
Happstack Crash Course.

The advice given to me is that I need to have two pages generated. A
ServerPart Response is a page. One page will setup the form to collect a
proposition from the student and post it, and the next page will parse that
information and generate a Response page, which will display whether the
proposition is correct or incorrect, and possibly provide feedback.

Possibly use 'lookInput' with the RqData monad. It actually turned out that I
could just use 'look'.

I will need to process the string I get and then display the result.

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

import Myitautology as T
\end{code}

For now I will import my tautology check until I can further understand how
happstack works.

\begin{code}
main :: IO ()
main = simpleHTTP nullConf $ propcheck
\end{code}

For 'dir "feedback"' has methodM POST attached to it in order match on the
the specific HTTP request, and if it does match, then produce the page.
This way, anyone trying to make a request on 'feedback' will in
this case go back to the home page.  Alternatively, we can nest another msum in
'dir "feedback"' and generate an error message that refers to specifically to
this case. I have taken this approach because it allows me to decide if in the
future I decide to remove the 'errorPage' or add more possibilities simply by
adding or subtratcing elements from the nested msum.

nullDir will check if the path is non-empty, and if it is, it the handler will
move onto the next item, which is notExist, my personalized 404 message. I
prefer my own, because I believe it can add a sense of user-friendliness.

It's interesting to note, that since I am using overloaded strings to make life
easier using blazeHtml, the string "/" needs to have it's type declared
explicitly because it doesn't know which type to choose. Another way around this
is to move propCheck into separate module, in order to avoid having to declare
the types explicitly, and this will be preferred when the website becomes more
complex, in order to have cleaner code.

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

  --       , seeOther ("/" :: String) (toResponse ("/" :: String))

\begin{code}
propForm :: ServerPart Response
propForm = ok $ toResponse $
    html $ do
      B.head $ do
        title "Upload Form"
      B.h1 $ do
        text "Peter's Mega Ultra Propositional Checker"
      B.body $ do
        p (string $ question1)
      B.div $ do
        
      B.div $ do
        p "Enter a proposition if you dare."
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/feedback" $ do
             input ! type_ "text" ! name "user_prop" ! size "40" ! maxlength "40"
             input ! type_ "submit" ! name "check_prop" ! value "Check this proposition"
             input ! type_ "reset" ! name "clear_prop" ! value "Clear"

question1 :: String
question1 =  "[...] the king explained to the prisoner that each of the two "
          ++ "rooms contained either a lady or a tiger, but it could be that "
          ++ "there were tigers in both rooms, or ladies in both rooms, or "
          ++ "then again, maybe one room contained a lady and the other room "
          ++ "a tiger."       
\end{code}

So far, I know how to get data from a form and display it, as well as do any
necessary calculations that gives me a value to display. My next problem is
getting the error message from the Parser in case the user enters a string
that can't be parsed, and displaying this error message to the user, which
should be helpful to the user.

Current Situation: 
\begin{enumerate}
        \item If a string that can't be parsed is encountered then 'feedback' does
           not load at all.
        \item I still need to organize the layout of my page and how responses for
           each case will be handled
\end{enumerate}

\begin{code}
feedback :: ServerPart Response
feedback = 
   do r <- getDataFn (defaultBodyPolicy "/tmp/" 1000 1000 1000) $ look "user_prop"
      ok $ toResponse $
         html $ do
           B.head $ do
             title "Prop Feedback"
           B.h2 $ do
             text "Feedback on given Proposition"           
             img ! src "/static/lambda.gif" ! alt "lambda" ! width "40" ! height "40"
           B.body $ do
             mkBody r
    where
      mkBody (Left errs) =
          do p $ "The following error occurred:"
             mapM_ (p . string) errs
      mkBody (Right theprop) = do
                p (string $ isTautology (T.isTaut (T.evalprop theprop)) theprop)


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

isTautology             :: Bool -> String -> String
isTautology True prop   =  "The proposition '" ++ prop ++ "' is a tautology."
isTautology _    prop   =  "The proposition '" ++ prop ++ "' is NOT a tautology."


\end{code}
