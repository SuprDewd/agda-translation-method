
module Translate.Solver.Reflection where

open import Reflection
open import Reflection public
  using ()
  renaming (_≟_ to _Term≟_)

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.Float


primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String

  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String


open import Data.Vec

-- Generated using https://github.com/SuprDewd/generate-agda-comparators

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _ = false

mutual

  absTermEq : Abs Term → Abs Term → Bool
  absTermEq (abs l1 l2) (abs r1 r2) = primStringEquality l1 r1 ∧ termEq l2 r2

  argPatternEq : Arg Pattern → Arg Pattern → Bool
  argPatternEq (arg l1 l2) (arg r1 r2) = argInfoEq l1 r1 ∧ patternEq l2 r2

  argTermEq : Arg Term → Arg Term → Bool
  argTermEq (arg l1 l2) (arg r1 r2) = argInfoEq l1 r1 ∧ termEq l2 r2

  argInfoEq : Arg-info → Arg-info → Bool
  argInfoEq (arg-info l1 l2) (arg-info r1 r2) = visibilityEq l1 r1 ∧ relevanceEq l2 r2

  clauseEq : Clause → Clause → Bool
  clauseEq (clause l1 l2) (clause r1 r2) = listArgPatternEq l1 r1 ∧ termEq l2 r2
  clauseEq (absurd-clause l1) (absurd-clause r1) = listArgPatternEq l1 r1
  clauseEq _ _ = false

  listArgPatternEq : List (Arg Pattern) → List (Arg Pattern) → Bool
  listArgPatternEq [] [] = true
  listArgPatternEq (_∷_ l1 l2) (_∷_ r1 r2) = argPatternEq l1 r1 ∧ listArgPatternEq l2 r2
  listArgPatternEq _ _ = false

  listArgTermEq : List (Arg Term) → List (Arg Term) → Bool
  listArgTermEq [] [] = true
  listArgTermEq (_∷_ l1 l2) (_∷_ r1 r2) = argTermEq l1 r1 ∧ listArgTermEq l2 r2
  listArgTermEq _ _ = false

  listClauseEq : List Clause → List Clause → Bool
  listClauseEq [] [] = true
  listClauseEq (_∷_ l1 l2) (_∷_ r1 r2) = clauseEq l1 r1 ∧ listClauseEq l2 r2
  listClauseEq _ _ = false

  literalEq : Literal → Literal → Bool
  literalEq (nat l1) (nat r1) = natEq l1 r1
  literalEq (float l1) (float r1) = primFloatEquality l1 r1
  literalEq (char l1) (char r1) = primCharEquality l1 r1
  literalEq (string l1) (string r1) = primStringEquality l1 r1
  literalEq (name l1) (name r1) = primQNameEquality l1 r1
  literalEq (meta l1) (meta r1) = primMetaEquality l1 r1
  literalEq _ _ = false

  natEq : Nat → Nat → Bool
  natEq zero zero = true
  natEq (suc l1) (suc r1) = natEq l1 r1
  natEq _ _ = false

  patternEq : Pattern → Pattern → Bool
  patternEq dot dot = true
  patternEq absurd absurd = true
  patternEq (con l1 l2) (con r1 r2) = primQNameEquality l1 r1 ∧ listArgPatternEq l2 r2
  patternEq (var l1) (var r1) = primStringEquality l1 r1
  patternEq (lit l1) (lit r1) = literalEq l1 r1
  patternEq (proj l1) (proj r1) = primQNameEquality l1 r1
  patternEq _ _ = false

  relevanceEq : Relevance → Relevance → Bool
  relevanceEq relevant relevant = true
  relevanceEq irrelevant irrelevant = true
  relevanceEq _ _ = false

  sortEq : Sort → Sort → Bool
  sortEq unknown unknown = true
  sortEq (set l1) (set r1) = termEq l1 r1
  sortEq (lit l1) (lit r1) = natEq l1 r1
  sortEq _ _ = false

  termEq : Term → Term → Bool
  termEq unknown unknown = true
  termEq (var l1 l2) (var r1 r2) = natEq l1 r1 ∧ listArgTermEq l2 r2
  termEq (con l1 l2) (con r1 r2) = primQNameEquality l1 r1 ∧ listArgTermEq l2 r2
  termEq (def l1 l2) (def r1 r2) = primQNameEquality l1 r1 ∧ listArgTermEq l2 r2
  termEq (lam l1 l2) (lam r1 r2) = visibilityEq l1 r1 ∧ absTermEq l2 r2
  termEq (pat-lam l1 l2) (pat-lam r1 r2) = listClauseEq l1 r1 ∧ listArgTermEq l2 r2
  termEq (pi l1 l2) (pi r1 r2) = argTermEq l1 r1 ∧ absTermEq l2 r2
  termEq (sort l1) (sort r1) = sortEq l1 r1
  termEq (lit l1) (lit r1) = literalEq l1 r1
  termEq (meta l1 l2) (meta r1 r2) = primMetaEquality l1 r1 ∧ listArgTermEq l2 r2
  termEq _ _ = false

  visibilityEq : Visibility → Visibility → Bool
  visibilityEq visible visible = true
  visibilityEq hidden hidden = true
  visibilityEq instance′ instance′ = true
  visibilityEq _ _ = false

isLt : ∀ {n} → Vec Bool n → Vec Bool n → Bool
isLt [] [] = false
isLt (true ∷ xs) (_ ∷ ys) = isLt xs ys
isLt (false ∷ xs) (y ∷ ys) = y

mutual

  primCharLess : Char → Char → Bool
  primCharLess x y = natLt (primCharToNat x) (primCharToNat y)

  primStringLess : String → String → Bool
  primStringLess x y = listCharLt (primStringToList x) (primStringToList y)
    where
      listCharEq : List Char → List Char → Bool
      listCharEq [] [] = false
      listCharEq (x ∷ xs) (y ∷ ys) = primCharEquality x y ∧ listCharEq xs ys
      listCharEq _ _ = false

      listCharLt : List Char → List Char → Bool
      listCharLt [] [] = false
      listCharLt [] (_ ∷ _) = true
      listCharLt (_ ∷ _) [] = false
      listCharLt (x ∷ xs) (y ∷ ys) = isLt (primCharLess x y ∷ listCharLt xs ys ∷ []) (primCharEquality x y ∷ listCharEq xs ys ∷ [])

  absTermLt : Abs Term → Abs Term → Bool
  absTermLt (abs l1 l2) (abs r1 r2) = isLt (primStringEquality l1 r1 ∷ termEq l2 r2 ∷ []) (primStringLess l1 r1 ∷ termLt l2 r2 ∷ [])

  argPatternLt : Arg Pattern → Arg Pattern → Bool
  argPatternLt (arg l1 l2) (arg r1 r2) = isLt (argInfoEq l1 r1 ∷ patternEq l2 r2 ∷ []) (argInfoLt l1 r1 ∷ patternLt l2 r2 ∷ [])

  argTermLt : Arg Term → Arg Term → Bool
  argTermLt (arg l1 l2) (arg r1 r2) = isLt (argInfoEq l1 r1 ∷ termEq l2 r2 ∷ []) (argInfoLt l1 r1 ∷ termLt l2 r2 ∷ [])

  argInfoLt : Arg-info → Arg-info → Bool
  argInfoLt (arg-info l1 l2) (arg-info r1 r2) = isLt (visibilityEq l1 r1 ∷ relevanceEq l2 r2 ∷ []) (visibilityLt l1 r1 ∷ relevanceLt l2 r2 ∷ [])

  clauseLt : Clause → Clause → Bool
  clauseLt (clause l1 l2) (clause r1 r2) = isLt (listArgPatternEq l1 r1 ∷ termEq l2 r2 ∷ []) (listArgPatternLt l1 r1 ∷ termLt l2 r2 ∷ [])
  clauseLt (absurd-clause l1) (absurd-clause r1) = isLt (listArgPatternEq l1 r1 ∷ []) (listArgPatternLt l1 r1 ∷ [])
  clauseLt (clause _ _) (absurd-clause _) = true
  clauseLt _ _ = false

  listArgPatternLt : List (Arg Pattern) → List (Arg Pattern) → Bool
  listArgPatternLt [] [] = false
  listArgPatternLt (_∷_ l1 l2) (_∷_ r1 r2) = isLt (argPatternEq l1 r1 ∷ listArgPatternEq l2 r2 ∷ []) (argPatternLt l1 r1 ∷ listArgPatternLt l2 r2 ∷ [])
  listArgPatternLt [] (_∷_ _ _) = true
  listArgPatternLt _ _ = false

  listArgTermLt : List (Arg Term) → List (Arg Term) → Bool
  listArgTermLt [] [] = false
  listArgTermLt (_∷_ l1 l2) (_∷_ r1 r2) = isLt (argTermEq l1 r1 ∷ listArgTermEq l2 r2 ∷ []) (argTermLt l1 r1 ∷ listArgTermLt l2 r2 ∷ [])
  listArgTermLt [] (_∷_ _ _) = true
  listArgTermLt _ _ = false

  listClauseLt : List Clause → List Clause → Bool
  listClauseLt [] [] = false
  listClauseLt (_∷_ l1 l2) (_∷_ r1 r2) = isLt (clauseEq l1 r1 ∷ listClauseEq l2 r2 ∷ []) (clauseLt l1 r1 ∷ listClauseLt l2 r2 ∷ [])
  listClauseLt [] (_∷_ _ _) = true
  listClauseLt _ _ = false

  literalLt : Literal → Literal → Bool
  literalLt (nat l1) (nat r1) = isLt (natEq l1 r1 ∷ []) (natLt l1 r1 ∷ [])
  literalLt (float l1) (float r1) = isLt (primFloatEquality l1 r1 ∷ []) (primFloatLess l1 r1 ∷ [])
  literalLt (char l1) (char r1) = isLt (primCharEquality l1 r1 ∷ []) (primCharLess l1 r1 ∷ [])
  literalLt (string l1) (string r1) = isLt (primStringEquality l1 r1 ∷ []) (primStringLess l1 r1 ∷ [])
  literalLt (name l1) (name r1) = isLt (primQNameEquality l1 r1 ∷ []) (primQNameLess l1 r1 ∷ [])
  literalLt (meta l1) (meta r1) = isLt (primMetaEquality l1 r1 ∷ []) (primMetaLess l1 r1 ∷ [])
  literalLt (nat _) (float _) = true
  literalLt (nat _) (char _) = true
  literalLt (nat _) (string _) = true
  literalLt (nat _) (name _) = true
  literalLt (nat _) (meta _) = true
  literalLt (float _) (char _) = true
  literalLt (float _) (string _) = true
  literalLt (float _) (name _) = true
  literalLt (float _) (meta _) = true
  literalLt (char _) (string _) = true
  literalLt (char _) (name _) = true
  literalLt (char _) (meta _) = true
  literalLt (string _) (name _) = true
  literalLt (string _) (meta _) = true
  literalLt (name _) (meta _) = true
  literalLt _ _ = false

  natLt : Nat → Nat → Bool
  natLt zero zero = false
  natLt (suc l1) (suc r1) = isLt (natEq l1 r1 ∷ []) (natLt l1 r1 ∷ [])
  natLt zero (suc _) = true
  natLt _ _ = false

  patternLt : Pattern → Pattern → Bool
  patternLt dot dot = false
  patternLt absurd absurd = false
  patternLt (con l1 l2) (con r1 r2) = isLt (primQNameEquality l1 r1 ∷ listArgPatternEq l2 r2 ∷ []) (primQNameLess l1 r1 ∷ listArgPatternLt l2 r2 ∷ [])
  patternLt (var l1) (var r1) = isLt (primStringEquality l1 r1 ∷ []) (primStringLess l1 r1 ∷ [])
  patternLt (lit l1) (lit r1) = isLt (literalEq l1 r1 ∷ []) (literalLt l1 r1 ∷ [])
  patternLt (proj l1) (proj r1) = isLt (primQNameEquality l1 r1 ∷ []) (primQNameLess l1 r1 ∷ [])
  patternLt (con _ _) dot = true
  patternLt (con _ _) (var _) = true
  patternLt (con _ _) (lit _) = true
  patternLt (con _ _) (proj _) = true
  patternLt (con _ _) absurd = true
  patternLt dot (var _) = true
  patternLt dot (lit _) = true
  patternLt dot (proj _) = true
  patternLt dot absurd = true
  patternLt (var _) (lit _) = true
  patternLt (var _) (proj _) = true
  patternLt (var _) absurd = true
  patternLt (lit _) (proj _) = true
  patternLt (lit _) absurd = true
  patternLt (proj _) absurd = true
  patternLt _ _ = false

  relevanceLt : Relevance → Relevance → Bool
  relevanceLt relevant relevant = false
  relevanceLt irrelevant irrelevant = false
  relevanceLt relevant irrelevant = true
  relevanceLt _ _ = false

  sortLt : Sort → Sort → Bool
  sortLt unknown unknown = false
  sortLt (set l1) (set r1) = isLt (termEq l1 r1 ∷ []) (termLt l1 r1 ∷ [])
  sortLt (lit l1) (lit r1) = isLt (natEq l1 r1 ∷ []) (natLt l1 r1 ∷ [])
  sortLt (set _) (lit _) = true
  sortLt (set _) unknown = true
  sortLt (lit _) unknown = true
  sortLt _ _ = false

  termLt : Term → Term → Bool
  termLt unknown unknown = false
  termLt (var l1 l2) (var r1 r2) = isLt (natEq l1 r1 ∷ listArgTermEq l2 r2 ∷ []) (natLt l1 r1 ∷ listArgTermLt l2 r2 ∷ [])
  termLt (con l1 l2) (con r1 r2) = isLt (primQNameEquality l1 r1 ∷ listArgTermEq l2 r2 ∷ []) (primQNameLess l1 r1 ∷ listArgTermLt l2 r2 ∷ [])
  termLt (def l1 l2) (def r1 r2) = isLt (primQNameEquality l1 r1 ∷ listArgTermEq l2 r2 ∷ []) (primQNameLess l1 r1 ∷ listArgTermLt l2 r2 ∷ [])
  termLt (lam l1 l2) (lam r1 r2) = isLt (visibilityEq l1 r1 ∷ absTermEq l2 r2 ∷ []) (visibilityLt l1 r1 ∷ absTermLt l2 r2 ∷ [])
  termLt (pat-lam l1 l2) (pat-lam r1 r2) = isLt (listClauseEq l1 r1 ∷ listArgTermEq l2 r2 ∷ []) (listClauseLt l1 r1 ∷ listArgTermLt l2 r2 ∷ [])
  termLt (pi l1 l2) (pi r1 r2) = isLt (argTermEq l1 r1 ∷ absTermEq l2 r2 ∷ []) (argTermLt l1 r1 ∷ absTermLt l2 r2 ∷ [])
  termLt (sort l1) (sort r1) = isLt (sortEq l1 r1 ∷ []) (sortLt l1 r1 ∷ [])
  termLt (lit l1) (lit r1) = isLt (literalEq l1 r1 ∷ []) (literalLt l1 r1 ∷ [])
  termLt (meta l1 l2) (meta r1 r2) = isLt (primMetaEquality l1 r1 ∷ listArgTermEq l2 r2 ∷ []) (primMetaLess l1 r1 ∷ listArgTermLt l2 r2 ∷ [])
  termLt (var _ _) (con _ _) = true
  termLt (var _ _) (def _ _) = true
  termLt (var _ _) (lam _ _) = true
  termLt (var _ _) (pat-lam _ _) = true
  termLt (var _ _) (pi _ _) = true
  termLt (var _ _) (sort _) = true
  termLt (var _ _) (lit _) = true
  termLt (var _ _) (meta _ _) = true
  termLt (var _ _) unknown = true
  termLt (con _ _) (def _ _) = true
  termLt (con _ _) (lam _ _) = true
  termLt (con _ _) (pat-lam _ _) = true
  termLt (con _ _) (pi _ _) = true
  termLt (con _ _) (sort _) = true
  termLt (con _ _) (lit _) = true
  termLt (con _ _) (meta _ _) = true
  termLt (con _ _) unknown = true
  termLt (def _ _) (lam _ _) = true
  termLt (def _ _) (pat-lam _ _) = true
  termLt (def _ _) (pi _ _) = true
  termLt (def _ _) (sort _) = true
  termLt (def _ _) (lit _) = true
  termLt (def _ _) (meta _ _) = true
  termLt (def _ _) unknown = true
  termLt (lam _ _) (pat-lam _ _) = true
  termLt (lam _ _) (pi _ _) = true
  termLt (lam _ _) (sort _) = true
  termLt (lam _ _) (lit _) = true
  termLt (lam _ _) (meta _ _) = true
  termLt (lam _ _) unknown = true
  termLt (pat-lam _ _) (pi _ _) = true
  termLt (pat-lam _ _) (sort _) = true
  termLt (pat-lam _ _) (lit _) = true
  termLt (pat-lam _ _) (meta _ _) = true
  termLt (pat-lam _ _) unknown = true
  termLt (pi _ _) (sort _) = true
  termLt (pi _ _) (lit _) = true
  termLt (pi _ _) (meta _ _) = true
  termLt (pi _ _) unknown = true
  termLt (sort _) (lit _) = true
  termLt (sort _) (meta _ _) = true
  termLt (sort _) unknown = true
  termLt (lit _) (meta _ _) = true
  termLt (lit _) unknown = true
  termLt (meta _ _) unknown = true
  termLt _ _ = false

  visibilityLt : Visibility → Visibility → Bool
  visibilityLt visible visible = false
  visibilityLt hidden hidden = false
  visibilityLt instance′ instance′ = false
  visibilityLt visible hidden = true
  visibilityLt visible instance′ = true
  visibilityLt hidden instance′ = true
  visibilityLt _ _ = false
