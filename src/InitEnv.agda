--------------------------------------------------------------------------------
-- This file generates the environment that the interpreter starts with. In
-- particular, it contains the grammar that is loaded initially.
--------------------------------------------------------------------------------

module InitEnv where

open import Class.Map
open import Data.Char.Ranges
open import Data.List using (dropWhile; takeWhile)
open import Data.SimpleMap
open import Data.String using (fromList; toList)
open import Data.Word32

open import Prelude
open import Prelude.Strings

open import Parse.Escape
open import SimpleInductive

private

  nameSymbols : List Char
  nameSymbols = "$='-/!@&"

  nameInits : List Char
  nameInits = letters ++ "_"

  nameTails : List Char
  nameTails = nameInits ++ nameSymbols ++ digits

  parseConstrToNonTerminals : String → List String
  parseConstrToNonTerminals = (map fromList) ∘ parseConstrToNonTerminals' ∘ toList
    where
      parseConstrToNonTerminals' : List Char → List (List Char)
      parseConstrToNonTerminals' =
        takeEven ∘ (map concat) ∘ (splitMulti "_") ∘ groupEscaped -- don't split on escaped underscores!

  grammar : List (List Char)
  grammar =
    "space'$" ∷ "space'$=newline=_space'_" ∷ "space'$=space=_space'_" ∷
    "space$=newline=_space'_" ∷ "space$=space=_space'_" ∷

    "index'$" ∷ map (λ c → "index'$" ++ [ c ] ++ "_index'_") digits ++
    map (λ c → "index$" ++ [ c ] ++ "_index'_") digits ++
    "var$_string_" ∷ "var$_index_" ∷

    "sort$=ast=" ∷ "sort$=sq=" ∷
    "const$Char" ∷

    "term$_var_" ∷
    "term$_sort_" ∷
    "term$=Kappa=_const_" ∷
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
    "term$=zeta=EvalStmt_space__term_" ∷
    "term$=zeta=ShellCmd_space__term__space__term_" ∷
    "term$=zeta=CheckTerm_space__term__space__term_" ∷
    "term$=zeta=Parse_space__term__space__term__space__term_" ∷
    "term$=zeta=Normalize_space__term_" ∷
    "term$=zeta=HeadNormalize_space__term_" ∷
    "term$=zeta=CatchErr_space__term__space__term_" ∷ -- this is not actually in PrimMeta
    "term$=kappa=_char_" ∷ -- this constructs a Char
    "term$=gamma=_space__term__space__term_" ∷ -- charEq

    "lettail$=dot=" ∷ "lettail$=colon=_space'__term__space'_=dot=" ∷

    "stmt'$let_space__string__space'_=colon==equal=_space'__term__space'__lettail_" ∷
    "stmt'$ass_space__string__space'_=colon=_space'__term__space'_=dot=" ∷
    "stmt'$seteval_space__term__space__string__space__string__space'_=dot=" ∷
    "stmt'$import_space__string__space'_=dot=" ∷
    "stmt'$" ∷
    "stmt$_space'__stmt'_" ∷
    []

  sortGrammar : List (List Char) → SimpleMap (List Char) (List (List Char))
  sortGrammar G = mapSnd (map (dropHeadIfAny ∘ dropWhile (¬? ∘ _≟ '$'))) $
    mapFromList (takeWhile (¬? ∘ _≟ '$')) G

  toInductiveData : String → String → List String → InductiveData
  toInductiveData namespace name constrs =
    (namespace + "$" + name
    , map (λ c → (namespace + "$" + name + "$" + c , map (toConstrData' name) (parseConstrToNonTerminals c)))
          constrs)
    where
      toConstrData' : String → String → ConstrData'
      toConstrData' self l = if self ≣ l then Self else Other (namespace + "$" + l)

  stringData : InductiveData
  stringData =
    ("init$string"
    , ("init$string$cons" , (Other "ΚChar" ∷ Self ∷ [])) ∷ ("init$string$nil" , []) ∷ []) -- capital kappa

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

  charDataConstructor : Char → String → String
  charDataConstructor c prefix =
    "let " + prefix + fromList (escapeChar c) + " := κ" + show c + "."

  nameInitConstrs : List String
  nameInitConstrs = map (flip charDataConstructor "init$nameInitChar$") nameInits

  nameTailConstrs : List String
  nameTailConstrs = map (flip charDataConstructor "init$nameTailChar$") nameTails

  initEnvConstrs : List InductiveData
  initEnvConstrs = stringData ∷
    (map
      (λ { (name , rule) → toInductiveData "init" (fromList name) (map fromList rule) }) $
      sortGrammar grammar)

  otherInit : List String
  otherInit =
    map simpleInductive (stringListData ∷ termListData ∷ metaResultData ∷ [])
    ++ "let init$string$_nameInitChar__string'_ := init$string$cons."
    ∷ "let init$string'$_nameTailChar__string'_ := init$string$cons."
    ∷ "let init$string'$ := init$string$nil."
    ∷ "let eval := λ s : init$stmt ζEvalStmt s." ∷ "seteval eval init stmt." ∷ []

  grammarWithChars : List (List Char)
  grammarWithChars = grammar ++
    map ("nameTailChar$" ++_) (map escapeChar nameTails) ++
    map ("nameInitChar$" ++_) (map escapeChar nameInits) ++
    "char$!!" ∷
    "string'$_nameTailChar__string'_" ∷ "string'$" ∷
    "string$_nameInitChar__string'_" ∷
    "var$_string_" ∷ "var$_index_" ∷ []

--------------------------------------------------------------------------------

initEnv : String
initEnv = "let init$char := ΚChar." + Data.String.concat
  (map simpleInductive initEnvConstrs ++ nameInitConstrs ++ nameTailConstrs ++ otherInit)

-- a map from non-terminals to their possible expansions
parseRuleMap : SimpleMap (List Char) (List (List Char))
parseRuleMap = from-just $ sequence $ map (λ { (fst , snd) → do
  snd' ← sequence (map (λ x → translate $ fst ++ "$" ++ x) snd)
  return (fst , reverse snd') }) $ sortGrammar grammarWithChars

coreGrammarGenerator : List (List Char)
coreGrammarGenerator = from-just $ sequence $ map translate grammarWithChars
