module Ring where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong)
  open import Data.Nat
  open import Data.Nat.Tactic.RingSolver

  --open import AlmostCommutativeRing ring

  *-dance : ∀ ( a b c d : ℕ) → a * b * c * d ≡ a * c * (b * d)
  *-dance a b c d = {!solve-∀!}
