--------------------------------------------------------------------------------
-- This file generates the environment that the interpreter starts with. In
-- particular, it contains the grammar that is loaded initially.
--------------------------------------------------------------------------------

module Bootstrap.InitEnv where

open import Prelude
open import Prelude.Strings

open import Class.Listable
open import Class.Map
open import Data.Char.Ranges
open import Data.List using (dropWhile; takeWhile)
open import Data.SimpleMap
open import Data.String using (fromList; toList)

open import Bootstrap.SimpleInductive
open import Parse.Escape
open import Theory.PrimMeta

inNT : String → String → String
inNT nt rhs = nt + "$" + rhs

genSimple : String → ℕ → String
genSimple symb args = symb + concat (replicate args "^space^_term_")

genBinder : String → String
genBinder symb = symb + "^space^_string_^space'^=colon=^space'^_term_^space^_term_"

genBuiltin : String → ℕ → String
genBuiltin name = genSimple ("=zeta=" + name)

genBuiltin' : PrimMeta → String
genBuiltin' m = genBuiltin (show m) (primMetaArity m)

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
      parseConstrToNonTerminals' = takeEven ∘ (splitMulti '_')
        -- this also ignores ignored non-terminals automatically

  grammar : List String
  grammar =
    "space'$" ∷ "space'$=newline=_space'_" ∷ "space'$=space=_space'_" ∷
    "space$=newline=_space'_" ∷ "space$=space=_space'_" ∷

    "index'$" ∷ map (λ c → fromList ("index'$" ++ [ c ] ++ "_index'_")) digits ++
    map (λ c → fromList ("index$" ++ [ c ] ++ "_index'_")) digits ++
    "var$_string_" ∷ "var$_index_" ∷

    "sort$=ast="  ∷ "sort$=sq=" ∷
    "const$CharT" ∷ "const$=kappa=_char_" ∷ "const$CharEq"   ∷
    "const$MM"    ∷ "const$MuM"           ∷ "const$EpsilonM" ∷ "const$CatchM" ∷

    (inNT "term" <$>
      "_var_" ∷ "_sort_" ∷ "=Kappa=_const_" ∷
      genSimple "=pi="    1 ∷ genSimple "=psi=" 1 ∷ genSimple "=beta="  2 ∷ genSimple "=delta=" 2 ∷
      genSimple "=sigma=" 1 ∷ genSimple "=phi=" 3 ∷ genSimple "=equal=" 2 ∷
      "=lsquare=^space'^_term_^space^_term_^space'^=rsquare=" ∷
      "=langle=^space'^_term_^space^_term_^space'^=rangle=" ∷
      "=rho=^space^_term_^space^_string_^space'^=dot=^space'^_term_^space^_term_" ∷
      genBinder "=forall=" ∷ genBinder "=Pi="     ∷
      genBinder "=lambda=" ∷ genBinder "=Lambda=" ∷
      genBinder "=iota="   ∷
      "=lbrace=^space'^_term_^space'^=comma=^space'^_term_^space^_string_^space'^=dot=^space'^_term_^space'^=rbrace=" ∷

      genSimple "=omega=" 1 ∷ genSimple "=mu=" 2 ∷ genSimple "=epsilon=" 1 ∷ -- meta monad primitives

      map genBuiltin' (Listable.listing PrimMeta-Listable)) ++

    "lettail$=dot=" ∷ "lettail$=colon=^space'^_term_^space'^=dot=" ∷
    []

  sortGrammar : List String → SimpleMap String (List String)
  sortGrammar G = mapSnd (map (fromList ∘ dropHeadIfAny ∘ dropWhile (¬? ∘ _≟ '$'))) $
    mapFromList (fromList ∘ takeWhile (¬? ∘ _≟ '$')) $ map toList G

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
    , ("stringCons" , (Other "init$char" ∷ Self ∷ [])) ∷ ("stringNil" , []) ∷ []) -- capital kappa

  stringListData : InductiveData
  stringListData =
    ("init$stringList" ,
    ("stringListNil" , []) ∷ ("stringListCons" , (Other "init$string" ∷ Self ∷ [])) ∷ [])

  charDataConstructor : Char → String → String
  charDataConstructor c prefix =
    "let " + prefix + fromList (escapeChar c) + " := Κκ" + show c + "."

  nameInitConstrs : List String
  nameInitConstrs = map (flip charDataConstructor "init$nameInitChar$") nameInits

  nameTailConstrs : List String
  nameTailConstrs = map (flip charDataConstructor "init$nameTailChar$") nameTails

  initEnvConstrs : List InductiveData
  initEnvConstrs = stringData ∷ ((uncurry (toInductiveData "init")) <$> sortGrammar grammar)

  definedGrammar : List (String × String)
  definedGrammar =
    ("unit" , "∀ X : * Π _ : X X") ∷
    ("tt" , "Λ X : * λ x : X x") ∷
    ("string$_nameInitChar__string'_" , "stringCons") ∷
    ("string'$_nameTailChar__string'_" , "stringCons") ∷
    ("string'$" , "stringNil") ∷

    ("err" , "init$string") ∷

    ("stmt'$let^space^_string_^space'^=colon==equal=^space'^_term_^space'^_lettail_"
      , "λ s : init$string λ t : init$term λ lt : init$lettail
         [[<lt ω init$unit> ζLet s t] λ T : init$term ζAnnLet s t T]") ∷
    ("stmt'$seteval^space^_term_^space^_string_^space^_string_^space'^=dot="
      , "λ ev : init$term λ NT : init$string λ namespace : init$string ζSetEval ev NT namespace") ∷
    ("stmt'$runMeta^space^_term_^space'^=dot=" , "λ x : ω init$unit x") ∷
    ("stmt'$import^space^_string_^space'^=dot=" , "λ s : init$string ζImport s") ∷
    ("stmt'$" , "ε init$tt") ∷
    ("stmt$^space'^_stmt'_" , "λ x : ω init$unit x") ∷
    ("product" , "λ A : * λ B : * ∀ X : * Π _ : Π _ : A Π _ : B X X") ∷
    ("pair" , "λ A : * λ B : * λ a : A λ b : B Λ X : * λ p : Π _ : A Π _ : B X [[p a] b]") ∷
    []

  otherInit : List String
  otherInit =
    map simpleInductive (stringListData ∷ []) ++
    map (λ where (n , d) → "let init$" + n + " := " + d + ".") definedGrammar ++
    "let eval := λ x : ω init$unit x." ∷ "seteval eval init stmt." ∷ []

--------------------------------------------------------------------------------

grammarWithChars : List String
grammarWithChars = grammar ++
  map (λ c → fromList ("nameTailChar$" ++ escapeChar c)) nameTails ++
  map (λ c → fromList ("nameInitChar$" ++ escapeChar c)) nameInits ++
  map proj₁ definedGrammar ++
  "char$!!" ∷ []

initEnv : String
initEnv = "let init$char := ΚCharT." + Data.String.concat
  (map simpleInductive initEnvConstrs ++ nameInitConstrs ++ nameTailConstrs ++ otherInit)

-- a map from non-terminals to their possible expansions
parseRuleMap : SimpleMap String (List String)
parseRuleMap = map (map₂ reverse) $ sortGrammar grammarWithChars
