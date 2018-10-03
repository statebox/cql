module Parser.TypesideSpec where

import           Language.Parser.AQLParser
import           Language.Parser.Generator.Generator
import           Language.Parser.Types

-- base
import           Data.Char                           (toLower)
import           Data.List                           (intercalate)

-- hspec
import           Test.Hspec

-- megaparsec
import           Text.Megaparsec

-- QuickCheck
import           Test.QuickCheck

-- semigroups
import           Data.List.NonEmpty                  (fromList, toList)

spec :: Spec
spec = do
  describe "typesideLiteralSectionParser" $ do
    it "parses correctly an empty TypesideLiteralSection" $
      parse typesideLiteralSectionParser "" "" ==
      Right (TypesideLiteralSection [] [] [] [] [])
    specify "parses correctly a TypesideLiteralSection with imports" $
      forAll (listOf typesideImportGen) $ \typesideImports ->
        parse
          typesideLiteralSectionParser
          ""
          ("imports " ++ (unwords $ map show typesideImports)) ==
        Right (TypesideLiteralSection typesideImports [] [] [] [])
    specify "parses correctly a TypesideLiteralSection with types" $
      forAll (listOf typesideTypeIdGen) $ \typesideTypes ->
        parse
          typesideLiteralSectionParser
          ""
          ("types " ++ (unwords $ map show typesideTypes)) ==
        Right (TypesideLiteralSection [] typesideTypes [] [] [])
    specify "parses correctly a TypesideLiteralSection with constants" $
      withMaxSuccess 30 $
      forAll (listOf typesideConstantSigGen) $ \typesideConstants ->
        parse
          typesideLiteralSectionParser
          ""
          ("constants " ++ (unwords $ map show typesideConstants)) ==
        Right (TypesideLiteralSection [] [] typesideConstants [] [])
    specify "parses correctly a TypesideLiteralSection with functions" $
      withMaxSuccess 30 $
      forAll (listOf typesideFunctionSigGen) $ \typesideFunctions ->
        parse
          typesideLiteralSectionParser
          ""
          ("functions " ++ (unwords $ map show typesideFunctions)) ==
        Right (TypesideLiteralSection [] [] [] typesideFunctions [])
    specify "parses correctly a TypesideLiteralSection with equations" $
      withMaxSuccess 4 $
      forAll (listOf typesideEquationSigGen) $ \typesideEquations ->
        parse
          typesideLiteralSectionParser
          ""
          ("equations " ++ (unwords $ map show typesideEquations)) ==
        Right (TypesideLiteralSection [] [] [] [] typesideEquations)
    specify "parses correctly a TypesideLiteralSection with every piece" $
      withMaxSuccess 30 $
      forAll
        ((\a b c d {-e-} -> (a, b, c, d{-, e-}))
          <$> listOf1 typesideImportGen
          <*> listOf1 typesideTypeIdGen
          <*> listOf1 typesideConstantSigGen
          <*> listOf1 typesideFunctionSigGen
          -- <*> listOf1 typesideEquationSigGen
        ) $ \(typesideImports, typesideTypes, typesideConstants, typesideFunctions{-, typesideEquations-}) ->
        parse
          typesideLiteralSectionParser
          ""
          ("imports " ++
            (unwords $ map show typesideImports) ++
            " types " ++
            (unwords $ map show typesideTypes) ++
            " constants " ++
            (unwords $ map show typesideConstants) ++
            " functions " ++
            (unwords $ map show typesideFunctions) -- ++
          --  " equations " ++
          --  (unwords $ map show typesideEquations)
          )
        == Right
          (TypesideLiteralSection
            typesideImports
            typesideTypes
            typesideConstants
            typesideFunctions []
            -- typesideTypes
            -- typesideConstants
            -- typesideFunctions
            -- typesideEquations
          )

  describe "typesideImportParser" $ do
    it "parses correctly a TypesideImportSql" $
      parse typesideImportParser "" "sql" == Right TypesideImportSql
    specify "parser correctly a TypesideImportRef" $
      forAll (identifierGen `suchThat` (\s -> not (s == "sql"))) $ \name ->
        parse typesideImportParser "" name == Right (TypesideImportRef name)

  describe "typesideTypeIdParser" $ do
    it "parses correctly a TypesideTypeIdTrue" $
      parse typesideTypeIdParser "" "true" == Right TypesideTypeIdTrue
    it "parses correctly a TypesideTypeIdFalse" $
      parse typesideTypeIdParser "" "false" == Right TypesideTypeIdFalse
    specify "parses correctly a TypesideTypeId" $
      forAll
        (identifierGen `suchThat` (\s -> not (s == "true" || s == "false"))) $ \name ->
        parse typesideTypeIdParser "" name == Right (TypesideTypeId name)

  describe "typesideFnNameParser" $ do
    specify "parses correctly a TypesideFnNameBool" $
      forAll arbitrary $ \bool ->
        parse typesideFnNameParser "" (toLower <$> show bool)
          == Right (TypesideFnNameBool bool)
    specify "parses correctly a TypesideFnNameString" $
      forAll
        (identifierGen `suchThat` (\s -> not (s == "true" || s == "false"))) $ \name ->
        parse typesideFnNameParser "" name == Right (TypesideFnNameString name)

  describe "typesideConstantSigParser" $ do
    specify "parses correctly a TypesideConstantSig" $
      forAll ((\a b -> (a, b))
        <$> (fromList <$> listOf1 typesideConstantIdGen)
        <*> typesideTypeIdGen
      ) $ \(typesideConstantIds, typesideTypeId) ->
        parse typesideConstantSigParser "" ((unwords $ show <$> toList typesideConstantIds) ++ " : " ++ show typesideTypeId)
          == Right (TypesideConstantSig typesideConstantIds typesideTypeId)

  describe "typesideConstantIdParser" $ do
    specify "parses correctly a TypesideConstantIdBool" $
      forAll arbitrary $ \bool ->
        parse typesideConstantIdParser "" (toLower <$> show bool)
          == Right (TypesideConstantIdBool bool)
    -- specify "parses correctly a TypesideConstantIdText" $
    --   forAll textGen $ \string ->
    --     parse typesideConstantIdParser "" ("\"" ++ string ++ "\"")
    --       == Right (TypesideConstantIdText string)
    specify "parses correctly a TypesideConstantIdInteger" $
      forAll (arbitrary :: Gen Integer) $ \int ->
        parse typesideConstantIdParser "" (show int) == Right (TypesideConstantIdInteger int)
    specify "parses correctly a TypesideConstanteIdLowerId" $
      forAll lowerIdGen $ \name ->
        parse typesideConstantIdParser "" name == Right (TypesideConstantIdLowerId name)
    specify "parses correctly a TypesideConstanteIdUpperId" $
      forAll upperIdGen $ \name ->
        parse typesideConstantIdParser "" name == Right (TypesideConstantIdUpperId name)


  describe "typesideFunctionSigParser" $ do
    specify "parses correctly a TypesideFunctionSig" $
      forAll ((\a b c -> (a, b, c))
        <$> typesideFnNameGen
        <*> (fromList <$> listOf1 identifierGen)
        <*> identifierGen
      ) $ \(typesideFnName, typesideFnLocals, typesideFnTarget) ->
        parse typesideFunctionSigParser "" (show typesideFnName ++ " : " ++ (intercalate ", " $ toList typesideFnLocals) ++ " -> " ++ typesideFnTarget)
          == Right (TypesideFunctionSig typesideFnName typesideFnLocals typesideFnTarget)

  describe "typesideEquationSigParser" $ do
    specify "parses correctly a TypesideEquationSigForAll" $
      withMaxSuccess 1 $
      forAll ((\a b c -> (a, b, c))
        <$> (fromList <$> listOf1 typesideLocalGen)
        <*> typesideEvalGen
        <*> typesideEvalGen
      ) $ \(typesideLocals, typesideEvalLeft, typesideEvalRight) ->
        parse typesideEquationSigParser "" ("forall " ++ (intercalate "," $ show <$> toList typesideLocals) ++ " . " ++ (show typesideEvalLeft) ++ " = " ++ (show typesideEvalRight))
          == Right (TypesideEquationSigForAll typesideLocals typesideEvalLeft typesideEvalRight)
    specify "parses correctly a TypesideEquationSigEq" $
      withMaxSuccess 1 $
      forAll ((\a b -> (a, b))
        <$> typesideEvalGen
        <*> typesideEvalGen
      ) $ \(typesideEvalLeft, typesideEvalRight) ->
        parse typesideEquationSigParser "" (show typesideEvalLeft ++ " = " ++ show typesideEvalRight)
          == Right (TypesideEquationSigEq typesideEvalLeft typesideEvalRight)

  describe "typesideLocalParser" $ do
    specify "parses correctly an identifier" $
      forAll identifierGen $ \name ->
        parse typesideLocalParser "" name == Right (TypesideLocal name Nothing)
    specify "parses correctly an identifier with type" $
      forAll ((\a b -> (a, b))
        <$> identifierGen
        <*> identifierGen
      ) $ \(name, type') ->
        parse typesideLocalParser "" (name ++ " : " ++ type')
          == Right (TypesideLocal name $ Just type')

  describe "typesideEvalParser" $ do
    specify "parses correctly a TypesideEvalNumber" $
      forAll scientificGen $ \number ->
        parse typesideEvalParser "" (show number) == Right (TypesideEvalNumber number)
    specify "parses correctly a TypesideEvalGen" $
      forAll typesideLiteralGen $ \typesideLiteral ->
        parse typesideEvalParser "" (show typesideLiteral) == Right (TypesideEvalGen typesideLiteral)
    specify "parses correctly a TypesideEvalInfix" $
      withMaxSuccess 1 $
      forAll ((\a b c -> (a, b, c))
        <$> typesideEvalGen
        <*> typesideFnNameGen
        <*> typesideEvalGen
      ) $ \(typesideEvalLeft, typesideFnName, typesideEvalRight) ->
        parse typesideEvalParser "" ("(" ++ show typesideEvalLeft ++ " " ++ show typesideFnName ++ " " ++ show typesideEvalRight ++ ")")
          == Right (TypesideEvalInfix typesideEvalLeft typesideFnName typesideEvalRight)
    specify "parses correctly a TypesideEvalParen" $
      withMaxSuccess 1 $
      forAll ((\a b -> (a, b))
        <$> typesideFnNameGen
        <*> (fromList <$> listOf1 typesideEvalGen)
      ) $ \(typesideFnName, typesideEvals) ->
        parse typesideEvalParser "" ((show typesideFnName) ++ "(" ++ (intercalate "," $ show <$> toList typesideEvals) ++ ")")
          == Right (TypesideEvalParen typesideFnName typesideEvals)

  describe "typesideLiteralParser" $ do
    specify "parses correctly a TypesideLiteralLowerId" $
      forAll lowerIdGen $ \name ->
        parse typesideLiteralParser "" name == Right (TypesideLiteralLowerId name)
    specify "parses correctly a TypesideLiteralUpperId" $
      forAll upperIdGen $ \name ->
        parse typesideLiteralParser "" name == Right (TypesideLiteralUpperId name)
