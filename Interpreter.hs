{-# LANGUAGE LambdaCase, MultiWayIf #-}
{-# LANGUAGE MonadComprehensions, TupleSections #-}
module Primitives where

import System.Environment
import Text.Parsec.String.Expr
import Text.Parsec.String.Parsec (try)
import Text.Parsec.String.Char
import Data.Char
import Data.Maybe
import Text.Parsec.String.Combinator
import Control.Applicative ((<|>), many)
import Text.Parsec.String (Parser)
import Text.Parsec.Prim (skipMany)
import FunctionsAndTypesForParsing (regularParse, parseWithEof, parseWithLeftOver)
import Control.Monad
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Data.Traversable

data Primitive = SBool Bool
                  | SInt Int
                  | SString String
                  | Variable String
                  | Lambda [String] Expr
                  | SList [Expr] deriving Show



data Operand = Plus | Minus | Multi | Div | Equals deriving Show
data Expr = Value Primitive
              | ToEval Operand Expr Expr
              | Let Context Expr
              | If Expr Expr Expr
              | Begin [Expr] Expr
              | Define String Expr
              | Apply Expr [Expr]
              | SMap Expr Primitive
              deriving Show

type Context = Map.Map String Primitive

blank :: Parser Char
blank = space <|> char '\n'

skipBlank :: Parser ()
skipBlank = skipMany blank

(|+|) :: Primitive -> Primitive -> Either String Primitive
(SInt i1)   |+| (SInt i2) = return $ SInt $ i1 + i2
(SString s) |+| (SString s1) = return $  SString $ s <> s1
_ |+| _ = Left "wrong pattern"

(|*|) :: Primitive -> Primitive -> Either String Primitive
(SInt i1) |*| (SInt i2) = return $ SInt $ i1 * i2
_ |*| _ = Left "wrong pattern"

(|/|) :: Primitive -> Primitive -> Either String Primitive
(SInt i1) |/| (SInt i2) = return $ SInt $ i1 `div` i2
_ |/| _ = Left "wrong pattern"

(|-|) :: Primitive -> Primitive -> Either String Primitive
(SInt i1) |-| (SInt i2) = return $ SInt $ i1 - i2
_ |-| _ = Left "wrong pattern"

(|==|) :: Primitive -> Primitive -> Either String  Primitive
(SInt i1) |==| (SInt i2) = return $ SBool $ i1 == i2
(SString s1) |==| (SString s2) = return $ SBool $ s1 == s2
(SBool b1) |==| (SBool b2) = return $ SBool $ b1 == b2

keywords :: Map.Map String Primitive
keywords = Map.insert "true" (SBool True) . Map.insert "false" (SBool False) $ Map.empty

getFun Plus = (|+|)
getFun Minus = (|-|)
getFun Multi = (|*|)
getFun Div = (|/|)
getFun Equals = (|==|)

barse (Right p) = (flip runStateT) keywords . runExceptT $ evalT p

testFun :: ExceptT String (StateT String IO) String
testFun = return "a"

replTest :: ExceptT String (StateT String IO) String
replTest = do
            s <- liftIO getLine
            case s of
             "bye" -> return "bye"
             _ -> do
              st <- get
              a <- testFun
              let x = abc a
              liftIO $ putStrLn $ show a
              replTest

evalT :: Expr -> ExceptT String (StateT Context Identity) Primitive

evalT (Value (Variable s))  = do
                            ctx <- get
                            case Map.lookup s ctx of
                             Just x -> return $ x
                             _ -> throwError $ "use of undeclared variable: " <> s
evalT (Value p) = return p
evalT (ToEval op ex1 ex2) =  do
                              eval1 <- evalT ex1
                              eval2 <- evalT ex2
                              let fun = getFun op
                              case fun eval1 eval2 of
                                Right x -> return x
                                Left s -> throwError s
evalT (Let context expr) = do
                            state <- get
                            put $ state <> context
                            expr1 <- evalT expr
                            put state
                            return $ expr1
evalT (If pred if' else') = do
                              p <- evalT pred
                              --if p == SBool True
                              if True
                                then evalT if'
                                else evalT else'
evalT (Begin exs expr) = do
                          ctx <- get
                          updateState exs
                          evalT expr
                          where
                            updateState = forEach $ \(Define name ex') -> evalT ex' >>= modify . Map.insert name
evalT (Apply val args) = do
                          (argNames, expr) <- evalT val >>= match
                          evalArgs <- sequence $ fmap evalT args
                          let ctxEntries = zip argNames evalArgs
                          forEach (\(name, lambdaArg) -> (modify . (Map.insert name)) lambdaArg) ctxEntries
                          evalT expr
                          where
                            match :: Primitive -> ExceptT String (StateT Context Identity) ([String], Expr)
                            match (Lambda a e) = return (a, e)
                            match x = throwError $ show x
evalT (SMap (Value l@(Lambda [x] expr)) (SList (h:t))) = do
                                                    result <- evalT (Apply (Value l) [h])
                                                    list <- evalT (SMap (Value l) $ SList t)
                                                    case (result, list) of
                                                      (p, (SList l)) -> return $ SList $ (Value p):l
evalT (SMap (Value l@(Lambda [x] expr)) (SList [])) = return $ SList []

forEach f (h:t) = do
                   f h
                   forEach f t
forEach _ [] = return ()

eval :: Expr ->  Context ->  ExceptT String IO Primitive
eval (Value (Variable s))  ctx =  case Map.lookup s ctx of
                            Just x -> return x
                            _ -> throwError $ "use of undeclared variable: " <> s
eval (Value p) _ = return p
eval (ToEval op ex1 ex2) c = do
                              let fun = getFun op
                              eval1 <- eval ex1 c
                              eval2 <- eval ex2 c
                              case fun eval1 eval2 of
                                Right x -> return x
                                Left x -> throwError x
eval (Let context expr) ctx = eval expr (context <> ctx)
eval (If pred if' else') c = do
                            p <- eval pred c
                           -- if p == SBool True
                            if True
                              then eval if' c
                              else eval else' c
eval (Begin exs expr) ctx = (eval expr) =<< unrollDefine exs ctx
                              where
                              unrollDefine ((Define name expr):t) ctx' = do
                                e <- eval expr ctx'
                                let newContext = Map.insert name e ctx'
                                rec <- unrollDefine t newContext
                                return $ rec
                              unrollDefine [] ctx' = return $ ctx'
eval (Apply val args) ctx = do
                         lambda <- eval val ctx
                         case lambda of
                          (Lambda argNames expr) -> do
                             evalArgs <- sequence $ fmap ((flip eval) ctx) args
                             let ctxEntries = zip argNames evalArgs
                             let newContext = foldl (\acc (name, arg) -> Map.insert  name arg acc) ctx ctxEntries
                             eval expr newContext
                          _ -> throwError "apply can only be used on lambdas"
eval (SMap (Value l@(Lambda [x] expr)) (SList (h:t))) ctx = do
                                                    result <- eval (Apply (Value l) [h]) ctx
                                                    list <- eval (SMap (Value l) $ SList t) ctx
                                                    case (result, list) of
                                                      (p, (SList l)) -> return $ SList $ (Value p):l

eval (SMap (Value l@(Lambda [x] expr)) (SList [])) ctx = return $ SList []

eval' :: Expr -> Either String Primitive
eval' e = return $ SInt 4

repl = do
        liftIO $ putStrLn "Insert Code ples"
        code <- liftIO getLine
        parsed <- case regularParse parseExpr code of
          Right x -> return $ x
          Left x -> throwError $ show x
        result <- eval parsed keywords
        liftIO $ putStrLn $ show result
        repl

repl' :: ExceptT String IO Primitive
repl' = do
        liftIO $ putStrLn "Insert Code ples"
        code <- liftIO getLine
        result <- tryRight $ do
                    parsed <- toString $ regularParse parseExpr code
                    result' <- eval' parsed
                    return $ result'
        liftIO $ putStrLn $ show result
        repl'

tryRight :: Monad m => Either a b -> ExceptT a m b
tryRight (Right x) = return x
tryRight (Left z) = throwError z

toString (Left x) = Left $ show x
toString (Right x) = Right x

parseTest = do
            c <- lookAhead anyChar
            d <- (lookAhead $ char c >> anyChar)
            return $ (c,d)

parseExpr :: Parser Expr
parseExpr  = do
                skipBlank
                c <- lookAhead anyChar
                case c of
                              '(' -> parseBracket
                              _ -> (lookAhead $ many $ noneOf [' ']) >>= \l ->
                                    case l of
                                    "let" -> parseLet
                                    "if" -> parseIf
                                    "begin" -> parseBegin
                                    "define" -> parseDefine
                                    "lambda" -> Value <$> parseLambda
                                    "map" -> parseMap
                                    x | x `elem` ["+", "-", "*", "/", "="] -> parseEval
                                    _ -> Value <$> parsePrimitive
                where
                  parseBracket = do
                    char '('
                    expr <- parseExpr
                    c <- lookAhead $ skipBlank >> anyChar
                    case c of
                      ')' -> char ')' >> return expr
                      _ ->  do
                            args <- manyTill parseExpr $ char ')'
                            return $ Apply expr args



parseMap :: Parser Expr
parseMap = do
            string "map"
            lambda <- parseExpr
            skipBlank
            list <- parsePrimitive
            return $ SMap lambda list

parseEval :: Parser Expr
parseEval = do
              op <- parseOperator
              arg1 <- parseExpr
              arg2 <- parseExpr
              skipBlank
              return $ ToEval op arg1 arg2

parseOperator :: Parser Operand
parseOperator = do
                  skipBlank
                  c <- anyChar
                  return $ case c of
                           '+' -> Plus
                           '-' -> Minus
                           '/' -> Div
                           '*' -> Multi
                           '=' -> Equals

parsePrimitive :: Parser Primitive
parsePrimitive = do
                  c <- lookAhead anyChar
                  case c of
                    '"' -> parseString
                    x | x `elem` ['1'..'9'] -> parseNumber
                    '[' -> parseArray
                    _ -> parseVariable

parseArray :: Parser Primitive
parseArray = do
              char '['
              list <- many parseExpr
              char ']'
              return $ SList list

parseString :: Parser Primitive
parseString = char '"' >> ( fmap (\s -> SString s) (many letter)) <* char '"'

parseNumber :: Parser Primitive
parseNumber = do
               d <- many1 digit
               return $ SInt (read d :: Int)

parseVariable :: Parser Primitive
parseVariable = skipBlank >> ( (many1 alphaNum) >>= (return . Variable)) <* skipBlank


parseLet :: Parser Expr
parseLet = do
             string "let"
             skipBlank
             char '('
             map <- getMap Map.empty
             char ')'
             skipBlank
             expr <- parseExpr
             return $ Let map expr

parseIf :: Parser Expr
parseIf = do
           string "if"
           pred <- parseExpr
           ifVal <- parseExpr
           elseVal <- parseExpr
           return $ If pred ifVal elseVal

getMap :: (Map.Map String Primitive) -> Parser (Map.Map String Primitive)
getMap m = do
            skipBlank
            name <- many1 letter
            skipBlank
            value <- parsePrimitive
            let f = Map.insert name value
            c <- lookAhead anyChar
            if c == ')' then (return $ f m) else getMap $ f m

parseBegin :: Parser Expr
parseBegin = do
              string "begin"
              exprs <- manyTill parseExpr $ lookAhead $ char ')'
              return $ Begin (init exprs) (last exprs)

parseDefine :: Parser Expr
parseDefine = do
               string "define"
               skipBlank
               var <- many1 alphaNum
               expr <- parseExpr
               return $ Define var expr

parseLambda :: Parser Primitive
parseLambda = do
                string "lambda"
                skipBlank
                char '('
                args <- manyTill (many1 letter <* skipBlank) $ char ')'
                expr <- parseExpr
                return $ Lambda args expr