{-# LANGUAGE OverloadedStrings #-}

module AQLSpec where

import           Language.AQL
import           Language.Schema
import           Language.Term
import           Language.Typeside

--base
import           Data.Either            (isRight)
import           Data.Map.Strict        as Map
import           Data.Set               as Set
import           Prelude                hiding (EQ)

-- hspec
import           Test.Hspec

-- transformers
import           Control.Monad.IO.Class (liftIO)


spec :: Spec
spec = do
  it "processes correctly the example file Mapping.aql" $ do
    fileContent <- liftIO $ readFile ("examples/Mapping.aql" :: String)
    parsed <- pure $ runProg fileContent
    isRight parsed `shouldBe` True
  it "processes correctly the example file Employee.aql" $ do
    fileContent <- liftIO $ readFile ("examples/Employee.aql" :: String)
    parsed <- pure $ runProg fileContent
    isRight parsed `shouldBe` True
  it "processes correctly the example file Sigma.aql" $ do
    fileContent <- liftIO $ readFile ("examples/Sigma.aql" :: String)
    parsed <- pure $ runProg fileContent
    isRight parsed `shouldBe` True
  it "processes correctly the example file Delta.aql" $ do
    fileContent <- liftIO $ readFile ("examples/Delta.aql" :: String)
    parsed <- pure $ runProg fileContent
    isRight parsed `shouldBe` True
  it "processes correctly the example file Import.aql" $ do
    fileContent <- liftIO $ readFile ("examples/Import.aql" :: String)
    parsed <- pure $ runProg fileContent
    isRight parsed `shouldBe` True
  it "processes correctly the example file Congruence.aql" $ do
    fileContent <- liftIO $ readFile ("examples/Congruence.aql" :: String)
    parsed <- pure $ runProg fileContent
    isRight parsed `shouldBe` True
  -- print typesideDom
  -- print schemaOne
  -- print schemaTwo
  -- print mappingTwoToOne
  -- print instanceOne

--------------------------------------------------------------------------------

schemaOne :: (Eq var, Eq fk) => Schema var String String String fk String
schemaOne =
  Schema typesideDom (Set.singleton "A") Map.empty atts' Set.empty Set.empty (\_ (EQ (lhs, rhs)) -> lhs == rhs)
  where
    atts' = Map.fromList [ ("A_att", ("A", "Dom")) ]

schemaTwo :: Eq var => Schema var String String String String String
schemaTwo =
  Schema typesideDom (Set.fromList ["A", "B"]) atts' atts'' Set.empty Set.empty (\_ (EQ (lhs, rhs)) -> lhs == rhs)
  where
    atts'  = Map.fromList [ ("f"    , ("A", "B"  )) ]
    atts'' = Map.fromList [ ("A_att", ("A", "Dom"))
                         , ("B_att", ("B", "Dom"))
                         ]

--example typeside one sort Dom { c0 ,..., c100 }
typesideDom :: Eq var => Typeside var String String
typesideDom = Typeside (Set.singleton "Dom") sym Set.empty (\_ (EQ (lhs,rhs)) -> lhs == rhs)
  where sym = sym' 100

        sym' :: Integer -> Map String ([String], String)
        sym' 0 = Map.empty
        sym' n = Map.insert ("c" ++ show n) ([], "Dom") $ sym' (n-1)

--------------------------------------------------------------------------------

-- instanceOne = Instance schemaOne
--   (Map.insert "g1" "A" Map.empty) Map.empty Set.empty (\(EQ (lhs,rhs)) -> lhs == rhs)
--   $ Algebra schemaOne (Map.fromList [("A", Set.singleton "x")])
--     (Map.empty) (Map.fromList [("A_att", Map.fromList [("x",Sym "c42" [])])])
--     (\t -> "x") (\t -> Gen "g1") (\t -> Sym "c42" []) (\t -> Sym "c42" [])

--------------------------------------------------------------------------------

-- mappingTwoToOne = Mapping schemaTwo schemaOne
--   (Map.fromList [("B", "A"), ("A","A")])
--   (Map.fromList [("f", Var ())])
--   (Map.fromList [("A_att", Att "att" (Var ())), ("B_att", Att "att" (Var ()))])
