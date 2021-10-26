--------------------------------------------------------------------------------
-- This file generates the environment that the interpreter starts with. In
-- particular, it contains the grammar that is loaded initially.
--------------------------------------------------------------------------------

module Bootstrap.InitEnv where

open import Class.Map
open import Data.Char.Ranges
open import Data.List using (dropWhile; takeWhile)
open import Data.SimpleMap
open import Data.String using (fromList; toList)

open import Prelude
open import Prelude.Strings

open import Parse.Escape
open import Bootstrap.SimpleInductive

private
  nameSymbols : List Char
  nameSymbols = "$='-/!@&^"

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
        -- this also ignores ignored non-terminals automatically

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
    "term$=pi=^space^_term_" ∷
    "term$=psi=^space^_term_" ∷
    "term$=beta=^space^_term_^space^_term_" ∷
    "term$=delta=^space^_term_^space^_term_" ∷
    "term$=sigma=^space^_term_" ∷
    "term$=lsquare=^space'^_term_^space^_term_^space'^=rsquare=" ∷
    "term$=langle=^space'^_term_^space^_term_^space'^=rangle=" ∷
    "term$=rho=^space^_term_^space^_string_^space'^=dot=^space'^_term_^space^_term_" ∷
    "term$=forall=^space^_string_^space'^=colon=^space'^_term_^space^_term_" ∷
    "term$=Pi=^space^_string_^space'^=colon=^space'^_term_^space^_term_" ∷
    "term$=iota=^space^_string_^space'^=colon=^space'^_term_^space^_term_" ∷
    "term$=lambda=^space^_string_^space'^=colon=^space'^_term_^space^_term_" ∷
    "term$=Lambda=^space^_string_^space'^=colon=^space'^_term_^space^_term_" ∷
    "term$=lbrace=^space'^_term_^space'^=comma=^space'^_term_^space^_string_^space'^=dot=^space'^_term_^space'^=rbrace=" ∷
    "term$=phi=^space^_term_^space^_term_^space^_term_" ∷
    "term$=equal=^space^_term_^space^_term_" ∷
    "term$=omega=^space^_term_" ∷ -- this is M
    "term$=mu=^space^_term_^space^_term_" ∷
    "term$=epsilon=^space^_term_" ∷
    "term$=zeta=EvalStmt^space^_term_" ∷
    "term$=zeta=ShellCmd^space^_term_^space^_term_" ∷
    "term$=zeta=CheckTerm^space^_term_^space^_term_" ∷
    "term$=zeta=Parse^space^_term_^space^_term_^space^_term_" ∷
    "term$=zeta=Normalize^space^_term_" ∷
    "term$=zeta=HeadNormalize^space^_term_" ∷
    "term$=zeta=CatchErr^space^_term_^space^_term_" ∷ -- this is not actually in PrimMeta
    "term$=kappa=_char_" ∷ -- this constructs a Char
    "term$=gamma=^space^_term_^space^_term_" ∷ -- charEq

    "lettail$=dot=" ∷ "lettail$=colon=^space'^_term_^space'^=dot=" ∷

    "stmt'$let^space^_string_^space'^=colon==equal=^space'^_term_^space'^_lettail_" ∷
    "stmt'$ass^space^_string_^space'^=colon=^space'^_term_^space'^=dot=" ∷
    "stmt'$seteval^space^_term_^space^_string_^space^_string_^space'^=dot=" ∷
    "stmt'$import^space^_string_^space'^=dot=" ∷
    "stmt'$" ∷
    "stmt$^space'^_stmt'_" ∷
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
    ∷ "let init$product := λ A : * λ B : * ∀ X : * Π _ : Π _ : A Π _ : B X X."
    ∷ "let init$pair := λ A : * λ B : * λ a : A λ b : B Λ X : * λ p : Π _ : A Π _ : B X [[p a] b]."
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
