--------------------------------------------------------------------------------
-- This file generates the environment that the interpreter starts with. In
-- particular, it contains the grammar that is loaded initially.
--------------------------------------------------------------------------------

module InitEnv where

open import Class.Map
open import Class.Traversable
open import Data.Char.Ranges
open import Data.List
open import Data.SimpleMap
open import Data.String using (fromList; toList)
open import Data.Word32

open import Prelude
open import Prelude.Strings

open import Escape
open import SimpleInductive

private

  nameSymbols : List Char
  nameSymbols = "$='-/!@&"

  nameInits : List Char
  nameInits = letters ++ "_"

  nameTails : List Char
  nameTails = nameInits ++ nameSymbols ++ digits

  parseConstrToNonTerminals : String -> List String
  parseConstrToNonTerminals = (map fromList) ∘ parseConstrToNonTerminals' ∘ toList
    where
      parseConstrToNonTerminals' : List Char -> List (List Char)
      parseConstrToNonTerminals' =
        takeEven ∘ (map concat) ∘ (splitMulti "_") ∘ groupEscaped -- don't split on escaped underscores!

  grammar : List (List Char)
  grammar =
    "space'$" ∷ "space'$=newline=_space'_" ∷ "space'$=space=_space'_" ∷
    "space$=newline=_space'_" ∷ "space$=space=_space'_" ∷

    "index'$" ∷ map (λ c -> "index'$" ++ [ c ] ++ "_index'_") digits ++
    map (λ c -> "index$" ++ [ c ] ++ "_index'_") digits ++
    "var$_string_" ∷ "var$_index_" ∷

    "sort$=ast=" ∷ "sort$=sq=" ∷

    "term$_var_" ∷
    "term$_sort_" ∷
    "term$=pi=_space__term_" ∷
    "term$=psi=_space__term_" ∷
    "term$=beta=_space__term__space__term_" ∷
    "term$=delta=_space__term__space__term_" ∷
    "term$=sigma=_space__term_" ∷
    "term$=lsquare=_space'__term__space__term__space'_=rsquare=" ∷
    "term$=langle=_space'__term__space__term__space'_=rangle=" ∷
    "term$=rho=_space__term__space__string__space'_=dot=_space'__term__space__term_" ∷
    "term$=forall=_space__string__space'_=colon=_space'__term__space__term_" ∷
    "term$=Pi=_space__string__space'_=colon=_space'__term__space__term_" ∷
    "term$=iota=_space__string__space'_=colon=_space'__term__space__term_" ∷
    "term$=lambda=_space__string__space'_=colon=_space'__term__space__term_" ∷
    "term$=Lambda=_space__string__space'_=colon=_space'__term__space__term_" ∷
    "term$=lbrace=_space'__term__space'_=comma=_space'__term__space__string__space'_=dot=_space'__term__space'_=rbrace=" ∷
    "term$=phi=_space__term__space__term__space__term_" ∷
    "term$=equal=_space__term__space__term_" ∷
    "term$=omega=_space__term_" ∷ -- this is M
    "term$=mu=_space__term__space__term_" ∷
    "term$=epsilon=_space__term_" ∷
    "term$=Alpha=_space__term_" ∷ -- this is zeta EvalStmt
    "term$=Beta=_space__term__space__term_" ∷ -- this is zeta ShellCmd
    "term$=Gamma=_space__term__space__term_" ∷ -- this is zeta CatchErr
    "term$=Delta=_space__term__space__term_" ∷ -- this is zeta CheckTerm

    "lettail$=dot=" ∷ "lettail$=colon=_space'__term__space'_=dot=" ∷

    "stmt'$let_space__string__space'_=colon==equal=_space'__term__space'__lettail_" ∷
    "stmt'$ass_space__string__space'_=colon=_space'__term__space'_=dot=" ∷
    "stmt'$normalize_space__term__space'_=dot=" ∷
    "stmt'$hnf_space__term__space'_=dot=" ∷
    "stmt'$erase_space__term__space'_=dot=" ∷
    "stmt'$test_space__term__space'_=dot=" ∷
    "stmt'$seteval_space__term__space__string__space__string__space'_=dot=" ∷
    "stmt'$import_space__string__space'_=dot=" ∷
    "stmt'$cmd_space__string__space'_=dot=" ∷
    "stmt'$" ∷
    "stmt$_space'__stmt'_" ∷
    []

  sortGrammar : List (List Char) -> SimpleMap (List Char) (List (List Char))
  sortGrammar G = mapSnd (map (dropHeadIfAny ∘ dropWhile (λ x -> ¬? (x ≟ '$')))) $
    mapFromList (takeWhile λ x -> ¬? (x ≟ '$')) G

  toInductiveData : String -> String -> List String -> InductiveData
  toInductiveData namespace name constrs =
    (namespace + "$" + name
    , map (λ c ->
             (namespace + "$" + name + "$" + c
             , (map (toConstrData' name) $ parseConstrToNonTerminals c)))
          constrs)
    where
      toConstrData' : String -> String -> ConstrData'
      toConstrData' self l = if self ≣ l then Self else Other (namespace + "$" + l)

  bitData : InductiveData
  bitData = "init$bit" , ("init$bit$true" , []) ∷ ("init$bit$false" , []) ∷ []

  byteData : InductiveData
  byteData =
    ("init$byte"
    , ("init$byte$bits"
      , ((Other "init$bit") ∷ (Other "init$bit") ∷ (Other "init$bit") ∷ (Other "init$bit") ∷
         (Other "init$bit") ∷ (Other "init$bit") ∷ (Other "init$bit") ∷ (Other "init$bit") ∷ [])) ∷ [])

  charData : InductiveData
  charData =
    ("init$char"
    , ("init$char$bytes"
      , ((Other "init$byte") ∷ (Other "init$byte") ∷ (Other "init$byte") ∷ (Other "init$byte") ∷ [])) ∷ [])

  stringData : InductiveData
  stringData =
    ("init$string"
    , ("init$string$cons" , (Other "init$char" ∷ Self ∷ [])) ∷ ("init$string$nil" , []) ∷ [])

  stringListData : InductiveData
  stringListData =
    ("init$stringList" ,
    ("init$stringList$nil" , []) ∷ ("init$stringList$cons" , (Other "init$string" ∷ Self ∷ [])) ∷ [])

  termListData : InductiveData
  termListData =
    ("init$termList"
    , ("init$termList$nil" , []) ∷ ("init$termList$cons" , (Other "init$term" ∷ Self ∷ [])) ∷ [])

  metaResultData : InductiveData
  metaResultData =
    ("init$metaResult"
    , ("init$metaResult$pair" , (Other "init$stringList" ∷ Other "init$termList" ∷ [])) ∷ [])

  bitToData : Bool -> String
  bitToData false = "init$bit$false"
  bitToData true = "init$bit$true"

  byteToData : Byte -> String
  byteToData (mkByte x0 x1 x2 x3 x4 x5 x6 x7) =
    "[[[[[[[[init$byte$bits " +
    bitToData x0 + "] " + bitToData x1 + "] " + bitToData x2 + "] " + bitToData x3 + "] " +
    bitToData x4 + "] " + bitToData x5 + "] " + bitToData x6 + "] " + bitToData x7 + "]"

  word32ToData : Word32 -> String
  word32ToData (mkWord32 x0 x1 x2 x3) =
    "[[[[init$char$bytes " +
    byteToData x0 + "] " + byteToData x1 + "] " + byteToData x2 + "] " + byteToData x3 + "]"

  charToData : Char -> String
  charToData c = word32ToData (charToWord32 c)

  charDataConstructor : Char -> String -> String
  charDataConstructor c prefix =
    "let " + prefix + (fromList $ escapeChar c) + " := " + charToData c + "."

  nameInitConstrs : List String
  nameInitConstrs = map (λ c -> charDataConstructor c "init$nameInitChar$") nameInits

  nameTailConstrs : List String
  nameTailConstrs = map (λ c -> charDataConstructor c "init$nameTailChar$") nameTails

  initEnvConstrs : List InductiveData
  initEnvConstrs = bitData ∷ byteData ∷ charData ∷ stringData ∷
    (map
      (λ { (name , rule) -> toInductiveData "init" (fromList name) (map fromList rule) }) $
      sortGrammar grammar)

  otherInit : List String
  otherInit =
    map simpleInductive (stringListData ∷ termListData ∷ metaResultData ∷ [])
    ++ "let init$string$_nameInitChar__string'_ := init$string$cons."
    ∷ "let init$string'$_nameTailChar__string'_ := init$string$cons."
    ∷ "let init$string'$ := init$string$nil."
    ∷ "let eval := λ s : init$stmt Α s." ∷ "seteval eval init stmt." ∷ []

  grammarWithChars : List (List Char)
  grammarWithChars = grammar ++
    map (λ c -> "nameTailChar$" ++ c) (map escapeChar nameTails) ++
    map (λ c -> "nameInitChar$" ++ c) (map escapeChar nameInits) ++
    "string'$_nameTailChar__string'_" ∷ "string'$" ∷ "string$_nameInitChar__string'_" ∷ "var$_string_" ∷ "var$_index_" ∷ []

--------------------------------------------------------------------------------

initEnv : String
initEnv = Data.String.concat
  (map simpleInductive initEnvConstrs ++ nameInitConstrs ++ nameTailConstrs ++ otherInit)

-- a map from non-terminals to their possible expansions
parseRuleMap : SimpleMap (List Char) (List (List Char))
parseRuleMap = from-just $ sequence $ map (λ { (fst , snd) -> do
  snd' <- sequence (map (λ x -> translate $ fst ++ "$" ++ x) snd)
  return (fst , reverse snd') }) $ sortGrammar grammarWithChars

coreGrammarGenerator : List (List Char)
coreGrammarGenerator = from-just $ sequence $ map translate grammarWithChars
