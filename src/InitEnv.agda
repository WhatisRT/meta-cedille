--------------------------------------------------------------------------------
-- This file generates the environment that the interpreter starts with. In
-- particular, it contains the grammar that is loaded initially.
--------------------------------------------------------------------------------

module InitEnv where

import Data.Maybe
open import Class.Map
open import Class.Traversable
open import Data.Char.Ranges
open import Data.List hiding (lookup)
open import Data.SimpleMap
open import Data.String using (fromList; toList)
open import Data.Word32

open import Prelude
open import Prelude.Strings

nameSymbols : List Char
nameSymbols = "$='-/!@&"

nameInits : List Char
nameInits = letters ++ "_"

nameTails : List Char
nameTails = nameInits ++ nameSymbols ++ digits

groupEscaped : List Char -> List (List Char)
groupEscaped = helper false
  where
    helper : Bool -> List Char -> List (List Char)
    helper b [] = []
    helper false (x ∷ l) = if ⌊ x ≟ '\\' ⌋ then helper true l else [ x ] ∷ helper false l
    helper true (x ∷ l) = ('\\' ∷ [ x ]) ∷ helper false l

data ConstrData' : Set where
  Self : ConstrData'
  Other : String -> ConstrData'

translationTable : SimpleMap String Char
translationTable =
  ("newline" , '\n') ∷ ("space" , ' ') ∷ ("ast" , '*') ∷ ("sq" , '□') ∷
  ("lparen" , '(') ∷ ("rparen" , ')') ∷ ("lbrace" , '{') ∷ ("rbrace" , '}') ∷
  ("lsquare" , '[') ∷ ("rsquare" , ']') ∷ ("langle" , '<') ∷ ("rangle" , '>') ∷
  ("equal" , '=') ∷ ("dot" , '.') ∷ ("comma" , ',') ∷ ("colon" , ':') ∷ ("semicolon" , ';') ∷
  ("question" , '?') ∷ ("exclamation" , '!') ∷ ("at" , '@') ∷ ("doublequote" , '"') ∷
  ("ampersand" , '&') ∷ ("backslash" , '\\') ∷ ("slash" , '/') ∷
  ("underscore" , '_') ∷ ("dollar" , '$') ∷ ("minus" , '-') ∷ ("forall" , '∀') ∷ ("exists" , '∃') ∷
  ("alpha" , 'α') ∷ ("beta" , 'β') ∷ ("gamma" , 'γ') ∷ ("delta" , 'δ') ∷ ("epsilon" , 'ε') ∷
  ("zeta" , 'ζ') ∷ ("eta" , 'η') ∷ ("theta" , 'θ') ∷ ("iota" , 'ι') ∷ ("kappa" , 'κ') ∷
  ("lambda" , 'λ') ∷ ("mu" , 'μ') ∷ ("nu" , 'ν') ∷ ("xi" , 'ξ') ∷ ("omicron" , 'ο') ∷ ("pi" , 'π') ∷
  ("rho" , 'ρ') ∷ ("varsigma" , 'ς') ∷ ("sigma" , 'σ') ∷ ("tau" , 'τ') ∷ ("upsilon" , 'υ') ∷
  ("phi" , 'φ') ∷ ("chi" , 'χ') ∷ ("psi" , 'ψ') ∷ ("omega" , 'ω') ∷
  ("Alpha" , 'Α') ∷ ("Beta" , 'Β') ∷ ("Gamma" , 'Γ') ∷ ("Delta" , 'Δ') ∷ ("Epsilon" , 'Ε') ∷
  ("Zeta" , 'Ζ') ∷ ("Eta" , 'Η') ∷ ("Theta" , 'Θ') ∷ ("Iota" , 'Ι') ∷ ("Kappa" , 'Κ') ∷
  ("Lambda" , 'Λ') ∷ ("Mu" , 'Μ') ∷ ("Nu" , 'Ν') ∷ ("Xi" , 'Ξ') ∷ ("Omicron" , 'Ο') ∷
  ("Pi" , 'Π') ∷ ("Rho" , 'Ρ') ∷ ("Varsigma" , 'Σ') ∷ ("Sigma" , 'Σ') ∷ ("Tau" , 'Τ') ∷
  ("Upsilon" , 'Υ') ∷ ("Phi" , 'Φ') ∷ ("Chi" , 'Χ') ∷ ("Psi" , 'Ψ') ∷ ("Omega" , 'Ω') ∷
  []

escapeTable : SimpleMap Char String
escapeTable = map swap translationTable

translate : List Char -> Maybe (List Char)
translate = (Data.Maybe.map concat) ∘ helper ∘ splitMulti '='
  where
    helper : List (List Char) -> Maybe (List (List Char))
    helper [] = just []
    helper (l ∷ []) = just (l ∷ [])
    helper (l ∷ l₁ ∷ l₂) = do
      l' <- (lookup (fromList l₁) translationTable)
      l'' <- helper l₂
      return $ l ∷
        (decCase l' of
          ('_' , "\\_") ∷ ('$' , "\\$") ∷ ('!' , "\\!") ∷ ('@' , "\\@") ∷ ('&' , "\\&") ∷ []
          default [ l' ]) ∷ l''

escape : List Char -> List Char
escape = concatMap λ c -> maybe (λ s -> "=" ++ toList s ++ "=") [ c ] $ lookup c escapeTable

ruleToConstr : List Char -> List Char
ruleToConstr = concat ∘ helper ∘ groupEscaped
  where
    helper : List (List Char) -> List (List Char)
    helper [] = []
    helper (l ∷ l₁) = (case l of λ
      { (c ∷ []) -> if c ≣ '$' ∨ c ≣ '_' ∨ c ≣ '!' ∨ c ≣ '@' ∨ c ≣ '&'
        then [ c ]
        else (maybe (λ s -> "=" ++ toList s ++ "=") [ c ] $ lookup c escapeTable)
      ; (_ ∷ c ∷ []) -> if l ≣ "\\$" ∨ l ≣ "\\_" ∨ l ≣ "\\!" ∨ l ≣ "\\@" ∨ l ≣ "\\&"
        then (maybe (λ s -> "=" ++ toList s ++ "=") [ c ] $ lookup c escapeTable)
        else l
      ; _ -> l }) ∷ (helper l₁)

ConstrData = String × List ConstrData'
InductiveData = String × List ConstrData

takeEven : ∀ {a} {A : Set a} -> List A -> List A
takeEven [] = []
takeEven (x ∷ []) = []
takeEven (x ∷ x₁ ∷ l) = x₁ ∷ takeEven l

parseConstrToNonTerminals' : List Char -> List (List Char)
parseConstrToNonTerminals' =
  takeEven ∘ (map concat) ∘ (splitMulti "_") ∘ groupEscaped -- don't split on escaped underscores!

parseConstrToNonTerminals : String -> List String
parseConstrToNonTerminals = (map fromList) ∘ parseConstrToNonTerminals' ∘ toList

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

grammar : List (List Char)
grammar =
  "space'$" ∷ "space'$=newline=_space'_" ∷ "space'$=space=_space'_" ∷
  "space$=newline=_space'_" ∷ "space$=space=_space'_" ∷

  "index'$" ∷ map (λ c -> "index'$" ++ [ c ] ++ "_index'_") digits ++
  map (λ c -> "index$" ++ [ c ] ++ "_index'_") digits ++
  "var$_name_" ∷ "var$_index_" ∷

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
  "term$=rho=_space__term__space__name__space'_=dot=_space'__term__space__term_" ∷
  "term$=forall=_space__name__space'_=colon=_space'__term__space__term_" ∷
  "term$=Pi=_space__name__space'_=colon=_space'__term__space__term_" ∷
  "term$=iota=_space__name__space'_=colon=_space'__term__space__term_" ∷
  "term$=lambda=_space__name__space'_=colon=_space'__term__space__term_" ∷
  "term$=Lambda=_space__name__space'_=colon=_space'__term__space__term_" ∷
  "term$=lbrace=_space'__term__space'_=comma=_space'__term__space__name__space'_=dot=_space'__term__space'_=rbrace=" ∷
  "term$=phi=_space__term__space__term__space__term_" ∷
  "term$=equal=_space__term__space__term_" ∷
  "term$=omega=_space__term_" ∷ -- this is M
  "term$=mu=_space__term__space__term_" ∷
  "term$=epsilon=_space__term_" ∷
  "term$=zeta=_space__term_" ∷ -- this is ev

  "lettail$=dot=" ∷ "lettail$=colon=_space'__term__space'_=dot=" ∷

  "stmt'$let_space__name__space'_=colon==equal=_space'__term__space'__lettail_" ∷
  "stmt'$ass_space__name__space'_=colon=_space'__term__space'_=dot=" ∷
  "stmt'$normalize_space__term__space'_=dot=" ∷
  "stmt'$hnf_space__term__space'_=dot=" ∷
  "stmt'$erase_space__term__space'_=dot=" ∷
  "stmt'$test_space__term__space'_=dot=" ∷
  "stmt'$seteval_space__term__space__name__space__name__space'_=dot=" ∷
  "stmt'$import_space__name__space'_=dot=" ∷
  "stmt'$cmd_space__term__space'_=dot=" ∷
  "stmt'$" ∷
  "stmt$_space'__stmt'_" ∷
  []

grammarWithChars : List (List Char)
grammarWithChars = grammar ++
  map (λ c -> "nameTailChar$" ++ c) (map (escape ∘ [_]) nameTails) ++
  map (λ c -> "nameInitChar$" ++ c) (map (escape ∘ [_]) nameInits) ++
  "name'$_nameTailChar__name'_" ∷ "name'$" ∷ "name$_nameInitChar__name'_" ∷ []

sortedGrammar : SimpleMap (List Char) (List (List Char))
sortedGrammar = mapSnd (map (dropHeadIfAny ∘ dropWhile (λ x -> ¬? (x ≟ '$')))) $
  mapFromList (takeWhile λ x -> ¬? (x ≟ '$')) grammar

sortedGrammarWithChars : SimpleMap (List Char) (List (List Char))
sortedGrammarWithChars = mapSnd (map (dropHeadIfAny ∘ dropWhile (λ x -> ¬? (x ≟ '$')))) $
  mapFromList (takeWhile λ x -> ¬? (x ≟ '$')) grammarWithChars

initEnvConstrsNoChars : List InductiveData
initEnvConstrsNoChars =
  map
    (λ { (name , rule) -> toInductiveData "init" (fromList name) (map fromList rule) })
    sortedGrammar

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

name'Data : InductiveData
name'Data =
  ("init$name'"
  , ("init$name'$_nameTailChar__name'_" , ((Other "init$char") ∷ Self ∷ [])) ∷
    ("init$name'$" , []) ∷
    [])

nameData : InductiveData
nameData =
  ("init$name" ,
  ("init$name$_nameInitChar__name'_" , ((Other "init$char") ∷ (Other "init$name'") ∷ [])) ∷ [])

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
  "let " + prefix + (fromList $ escape $ [ c ]) + " := " + charToData c + "."

nameInitConstrs : List String
nameInitConstrs = map (λ c -> charDataConstructor c "init$nameInitChar$") nameInits

nameTailConstrs : List String
nameTailConstrs = map (λ c -> charDataConstructor c "init$nameTailChar$") nameTails

initEnvConstrs : List InductiveData
initEnvConstrs = bitData ∷ byteData ∷ charData ∷ name'Data ∷ nameData ∷ initEnvConstrsNoChars

parseRuleMap' : Maybe (SimpleMap (List Char) (List (List Char)))
parseRuleMap' = sequence $ map (λ { (fst , snd) -> do
  snd' <- sequence (map (λ x -> translate $ fst ++ "$" ++ x) snd)
  return (fst , reverse snd') }) sortedGrammarWithChars

-- a map from non-terminals to their possible expansions
parseRuleMap : SimpleMap (List Char) (List (List Char))
parseRuleMap = from-just parseRuleMap'

module ConstrToString where

  constrDataToConstrType : String -> ConstrData -> String
  constrDataToConstrType name (n , []) = name
  constrDataToConstrType name (n , (Self ∷ constr)) =
    "Π _ : " + name + " " + constrDataToConstrType name (n , constr)
  constrDataToConstrType name (n , (Other x ∷ constr)) =
    "Π _ : " + x + " " + constrDataToConstrType name (n , constr)

  ℕ⊎Sshow : ℕ ⊎ String -> String
  ℕ⊎Sshow (inj₁ x) = show x
  ℕ⊎Sshow (inj₂ y) = y

  ℕ⊎Ssuc : ℕ ⊎ String -> ℕ ⊎ String
  ℕ⊎Ssuc (inj₁ x) = inj₁ (suc x)
  ℕ⊎Ssuc (inj₂ y) = inj₂ y

  constrDataToConstrPrefix : ℕ ⊎ String -> Char -> ConstrData -> String
  constrDataToConstrPrefix n c (name , []) = ""
  constrDataToConstrPrefix n c (name , x ∷ constr) =
    fromList (c ∷ []) + " _ : " + (case x of λ { Self → ℕ⊎Sshow n ; (Other y) → y }) +
    " " + constrDataToConstrPrefix (ℕ⊎Ssuc n) c (name , constr)

  constrDataToTypePrefix : ℕ ⊎ String -> Char -> ConstrData -> String
  constrDataToTypePrefix n c (name , []) = ℕ⊎Sshow n + " "
  constrDataToTypePrefix n c (name , x ∷ constr) =
    fromList (c ∷ []) + " _ : " + (case x of λ { Self → ℕ⊎Sshow n ; (Other y) → y }) +
    " " + constrDataToTypePrefix (ℕ⊎Ssuc n) c (name , constr)

  kthConstr : ℕ -> InductiveData -> String
  kthConstr k (name , constrs) with lookupMaybe k constrs
  kthConstr k (name , constrs) | Maybe.just c@(_ , constr) =
    constrDataToConstrPrefix (inj₂ name) 'λ' c + -- constructor arguments
    "Λ _ : * " +
    Data.String.concat
      (zipWith
        (λ constr k → "λ _ : " + constrDataToTypePrefix k 'Π' constr)
        constrs (applyUpTo inj₁ (length constrs))) + -- abstract arguments
    -- apply all abstract arguments to self constructors and leave the others alone
    -- then pass the results to the k-th abstract constructor
    applyTo currentConstr
      (zipWith
        (λ i -> λ
          { Self → applyTo
            ("<" + show i + " " + show (length constrs) + ">")
            abstractConstrs
          ; (Other x) → show i })
        (applyUpTo ((length constrs + length constr) ∸_) $ length constr) constr)
    where
      currentConstr = show (length constrs ∸ k ∸ 1)

      abstractConstrs : List String
      abstractConstrs = reverse $ applyUpTo (λ i -> show i) $ length constrs

      applyTo : String -> List String -> String
      applyTo f fs = foldl (λ s l -> "[" + s + " " + l + "]") f fs
  kthConstr k constrs | nothing = "Error: no such constructor"

  kthConstrType : String -> ℕ -> List ConstrData -> String
  kthConstrType name k constrs with lookupMaybe k constrs
  ... | just x = constrDataToConstrType name x
  ... | nothing = "Error: no such constructor"

  typeDecl : String -> List ConstrData -> String
  typeDecl name constrs =
    "∀ _ : * " +
    Data.String.concat
      (zipWith
        (λ constr k -> "Π _ : " + constrDataToTypePrefix k 'Π' constr)
        constrs
        (applyUpTo inj₁ (length constrs))) +
    show (length constrs)

  simpleInductive : InductiveData -> String
  simpleInductive d@(name , constrs) =
    "let " + name + " := " + typeDecl name constrs + "." +
    Data.String.concat
      (zipWith
        (λ constr k →
          "let " + proj₁ constr + " := " + kthConstr k d + " : " +
          kthConstrType name k constrs + ".")
        constrs
        (applyUpTo id (length constrs)))

open ConstrToString public

otherInit : List String
otherInit =
  map simpleInductive (stringData ∷ stringListData ∷ termListData ∷ metaResultData ∷ [])
  ++ "let eval := λ s : init$stmt ζ s." ∷ "seteval eval init stmt." ∷ []

initEnv : String
initEnv = Data.String.concat
  (map simpleInductive initEnvConstrs ++ nameInitConstrs ++ nameTailConstrs ++ otherInit)
