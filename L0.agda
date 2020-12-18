module L0 where

open import Common

-- Syntax

data Name : Set where
 d n j m : Name

data Pred1 : Set where
 M B : Pred1

data Pred2 : Set where
 K L : Pred2

data Expr : Set where
  _⦅_⦆ : Pred1 -> Name -> Expr
  _⦅_,_⦆ : Pred2 -> Name -> Name -> Expr
  ¬ : Expr -> Expr
  [_∧_] : Expr -> Expr -> Expr
  [_∨_] : Expr -> Expr -> Expr
  [_⇒_] : Expr -> Expr -> Expr
  [_⇔_] : Expr -> Expr -> Expr

example1 : Expr
example1 = [ K ⦅ d , j ⦆ ∧ M ⦅ d ⦆  ]
example2 : Expr
example2 = ¬ [ M ⦅ d ⦆ ∨ B ⦅ m ⦆ ]
example3 : Expr
example3 = [ L ⦅ n , j ⦆ ⇒ [ B ⦅ d ⦆ ∨ ¬ (K ⦅ m , m ⦆) ] ]
example4 : Expr
example4 = [ ¬ (¬ (¬ (B ⦅ n ⦆))) ⇔ ¬ (M ⦅ n ⦆) ]

-- Semantics
  
data Person : Set where
  Richard_Nixon : Person
  Noam_Chomsky : Person
  John_Mitchell : Person
  Muhammad_Ali : Person

instance
  eqPerson : Eq Person
  -- _==_ ⦃ eqPerson ⦄ x y =  isEq x y (refl {!x y!})
  _==_ ⦃ eqPerson ⦄ Richard_Nixon Richard_Nixon = true
  _==_ ⦃ eqPerson ⦄ Noam_Chomsky Noam_Chomsky = true
  _==_ ⦃ eqPerson ⦄ John_Mitchell John_Mitchell = true
  _==_ ⦃ eqPerson ⦄ Muhammad_Ali Muhammad_Ali = true
  _==_ ⦃ eqPerson ⦄ _ _ = false

_∈_ : {A : Set} {{_ : Eq A}} -> A -> PSet A -> Bool
x ∈ ⦃⦄ = false
x ∈ (x₁ :: xs) = (x == x₁) || (x ∈ xs)

⟦_⟧ₙ : Name -> Person
⟦ d ⟧ₙ = Richard_Nixon
⟦ n ⟧ₙ = Noam_Chomsky
⟦ j ⟧ₙ = John_Mitchell
⟦ m ⟧ₙ = Muhammad_Ali

⟦_⟧ₚ₁ : Pred1 -> PSet Person
⟦ x ⟧ₚ₁ = {!!}

⟦_⟧ₚ₂ : Pred2 -> PSet (Pair Person)
⟦ x ⟧ₚ₂ = {!!}

⟦_⟧ₑ : Expr -> Bool
{-# TERMINATING #-}
⟦ x ⦅ x₁ ⦆ ⟧ₑ = ⟦ x₁ ⟧ₙ ∈ ⟦ x ⟧ₚ₁ 
⟦ x ⦅ x₁ , x₂ ⦆ ⟧ₑ = < ⟦ x₁ ⟧ₙ , ⟦ x₂ ⟧ₙ > ∈ ⟦ x ⟧ₚ₂
⟦ ¬ x ⟧ₑ = neg ⟦ x ⟧ₑ
⟦ [ x ∧ x₁ ] ⟧ₑ = ⟦ x ⟧ₑ && ⟦ x₁ ⟧ₑ
⟦ [ x ∨ x₁ ] ⟧ₑ = ⟦ x ⟧ₑ || ⟦ x₁ ⟧ₑ
⟦ [ x ⇒ x₁ ] ⟧ₑ = (neg ⟦ x₁ ⟧ₑ) || ⟦ x ⟧ₑ
⟦ [ x ⇔ x₁ ] ⟧ₑ = ⟦ [ x ⇒ x₁ ] ⟧ₑ && ⟦ [ x₁ ⇒ x ] ⟧ₑ
