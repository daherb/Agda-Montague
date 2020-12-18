module L0E where

open import Common

-- Syntax

data Conj : Set  where
  and or : Conj

data N : Set where
  Saddie Liz Hank : N

data Vᵢ : Set where
  snores sleeps is-boring : Vᵢ

data Vₜ : Set where
  loves hates is-taller-than : Vₜ

data Neg : Set where
  it-is-not-the-case-that : Neg

data VP : Set where
  iv : Vᵢ -> VP
  tv : Vₜ -> N -> VP

data S : Set where
 sconjs : S -> Conj -> S -> S
 negs : Neg -> S -> S
 predvp : N -> VP -> S

example1 : S
example1 = predvp Saddie (iv snores)

example2 : S
example2 = predvp Liz (iv sleeps)

example3 : S
example3 = negs it-is-not-the-case-that (predvp Hank (iv snores))

example41 example42 : S
example41 = sconjs (sconjs (predvp Saddie (iv sleeps)) or (predvp Liz (iv is-boring))) and (predvp Hank (iv snores))
example42 = sconjs (predvp Saddie (iv sleeps)) or (sconjs (predvp Liz (iv is-boring)) and (predvp Hank (iv snores)))

example5 : S
example5 = negs it-is-not-the-case-that (negs it-is-not-the-case-that (predvp Saddie (iv sleeps)))

-- Semantics
  
data Individual : Set where
  Anwar_Sadat : Individual
  Queen_Elizabeth_II : Individual
  Henry_Kissinger : Individual

⟦_⟧N : N -> Individual
⟦ Saddie ⟧N = Anwar_Sadat
⟦ Liz ⟧N = Queen_Elizabeth_II
⟦ Hank ⟧N = Henry_Kissinger

⟦_⟧̬̬̌Vᵢ : Vᵢ -> Individual -> Bool
⟦ snores ⟧̬̬̌Vᵢ Anwar_Sadat = true
⟦ snores ⟧̬̬̌Vᵢ Queen_Elizabeth_II = true
⟦ snores ⟧̬̬̌Vᵢ Henry_Kissinger = false

⟦ sleeps ⟧̬̬̌Vᵢ Anwar_Sadat = true
⟦ sleeps ⟧̬̬̌Vᵢ Queen_Elizabeth_II = false
⟦ sleeps ⟧̬̬̌Vᵢ Henry_Kissinger = false

⟦ is-boring ⟧̬̬̌Vᵢ Anwar_Sadat = true
⟦ is-boring ⟧̬̬̌Vᵢ Queen_Elizabeth_II = true
⟦ is-boring ⟧̬̬̌Vᵢ Henry_Kissinger = true


⟦_⟧Vₜ : Vₜ -> Individual -> Individual -> Bool
⟦ loves ⟧Vₜ Anwar_Sadat _ = true
⟦ loves ⟧Vₜ Queen_Elizabeth_II Anwar_Sadat = false
⟦ loves ⟧Vₜ Queen_Elizabeth_II Queen_Elizabeth_II = true
⟦ loves ⟧Vₜ Queen_Elizabeth_II Henry_Kissinger = false
⟦ loves ⟧Vₜ Henry_Kissinger Anwar_Sadat = true
⟦ loves ⟧Vₜ Henry_Kissinger Queen_Elizabeth_II = false
⟦ loves ⟧Vₜ Henry_Kissinger Henry_Kissinger = true

⟦ hates ⟧Vₜ Anwar_Sadat _ = false
⟦ hates ⟧Vₜ Queen_Elizabeth_II Anwar_Sadat = true
⟦ hates ⟧Vₜ Queen_Elizabeth_II Queen_Elizabeth_II = false
⟦ hates ⟧Vₜ Queen_Elizabeth_II Henry_Kissinger = true
⟦ hates ⟧Vₜ Henry_Kissinger Anwar_Sadat = false
⟦ hates ⟧Vₜ Henry_Kissinger Queen_Elizabeth_II = true
⟦ hates ⟧Vₜ Henry_Kissinger Henry_Kissinger = false

⟦ is-taller-than ⟧Vₜ Anwar_Sadat Anwar_Sadat = false
⟦ is-taller-than ⟧Vₜ Anwar_Sadat Queen_Elizabeth_II = true
⟦ is-taller-than ⟧Vₜ Anwar_Sadat Henry_Kissinger = false
⟦ is-taller-than ⟧Vₜ Queen_Elizabeth_II _ = false
⟦ is-taller-than ⟧Vₜ Henry_Kissinger Anwar_Sadat = true
⟦ is-taller-than ⟧Vₜ Henry_Kissinger Queen_Elizabeth_II = true
⟦ is-taller-than ⟧Vₜ Henry_Kissinger Henry_Kissinger = false

⟦_⟧VP : VP -> Individual -> Bool
⟦ iv v ⟧VP = ⟦ v ⟧̬̬̌Vᵢ
⟦ tv v n ⟧VP = ⟦ v ⟧Vₜ ⟦ n ⟧N

⟦_⟧S : S -> Bool
⟦ sconjs x and x₂ ⟧S = ⟦ x ⟧S && ⟦ x₂ ⟧S
⟦ sconjs x or x₂ ⟧S = ⟦ x ⟧S || ⟦ x₂ ⟧S
⟦ negs x x₁ ⟧S = neg ⟦ x₁ ⟧S
⟦ predvp x x₁ ⟧S = ⟦ x₁ ⟧VP ⟦ x ⟧N
