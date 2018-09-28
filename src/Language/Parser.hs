module Language.Parser where

import Data.Map as Map
import Language.Common as C
import Language.Term as Term
import Language.Schema as S
import Language.Instance as I
import Language.Mapping as M
import Language.Typeside as T
import Language.Transform as Tr
import Language.Query as Q
import           Language.Parser.LexerRules
import           Language.Parser.Parser
import           Language.Parser.Types as Term'
import           Language.Parser.Typeside as T'
import           Language.Parser.Schema as S'
import           Data.List                  (foldl')
import           Data.Maybe
import           Text.Megaparsec
import           Data.List.NonEmpty 
import Language.Program as P


parseAqlProgram' :: Parser (String, Exp)
parseAqlProgram' = do x <- identifier
                      _ <- constant "="
                      y <- typesideExpParser
                      return $ (x, ExpTy y)
                   <|> 
                   do x <- identifier
                      _ <- constant "="
                      y <- schemaExpParser'
                      return $ (x, ExpS y)



toProg' :: [(String, Exp)] -> Prog
toProg' [] = newProg 
toProg' ((v,e):p) = case e of
   ExpTy ty -> KindCtx (Map.insert v ty t) s i m q tr ((v,TYPESIDE):o) 
   ExpS s' -> KindCtx t (Map.insert v s' s) i m q tr ((v,SCHEMA):o) 
   ExpI i' -> KindCtx t s (Map.insert v i' i) m q tr ((v,INSTANCE):o) 
   ExpM m' -> KindCtx t s i (Map.insert v m' m) q tr ((v,MAPPING):o)
   ExpQ q' -> KindCtx t s i m (Map.insert v q' q) tr ((v,QUERY):o)
   ExpT t' -> KindCtx t s i m q (Map.insert v t' tr) ((v,TRANSFORM):o)
  where KindCtx t s i m q tr o = toProg' p

parseAqlProgram :: String -> Err Prog
parseAqlProgram s = case runParser (many parseAqlProgram') "" s of
	Left err -> Left $ show err
	Right x -> pure $ toProg' x



