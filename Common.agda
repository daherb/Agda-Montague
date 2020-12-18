module Common where

data PSet (A : Set) : Set where
  ⦃⦄ :  PSet A
  _::_ : A -> PSet A -> PSet A

data Pair (A : Set) : Set where
  <_,_> : A -> A -> Pair A

data Bool : Set where
  true : Bool
  false : Bool

neg : Bool -> Bool
neg true = false
neg false = true

_&&_ : Bool -> Bool -> Bool
true && true = true
_ && _ = false

_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true

-- data _≡_ {a} {A : Set a} (x : A) : A → Set a where
--   instance refl : x ≡ x

-- data _≡_ {a} {A : Set a} : A → A → Set where
--   refl : (a : A) → a ≡ a
-- sym : ∀ x y → x ≡ y → y ≡ x
-- sym .a .a (refl a) = refl a
-- isEq : ∀ x y -> x ≡ y -> Bool
-- isEq .a .a (refl a) = true

record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

instance
  eqPair : {A : Set} {{_ : Eq A}} → Eq (Pair A)
  _==_ {{eqPair}} < x₁ , x₂ > < y₁ , y₂ > = (x₁ == y₁) && (x₂ == y₂)
