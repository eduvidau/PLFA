module Naturals where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)  

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

eight : ℕ
eight = 8

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
 begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
   suc (2 + 4)
  ≡⟨⟩
   suc (suc (1 + 4))
  ≡⟨⟩
   suc (suc (suc (0 + 4)))
  ≡⟨⟩
  suc (suc (suc 4))
  ≡⟨⟩
  7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_^_ : ℕ → ℕ  → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc_ : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

infixl 6  inc_
infixl 7  _O _I

_ : inc ⟨⟩ ≡ ⟨⟩ I 
_ = refl

_ : inc ⟨⟩ O  ≡ ⟨⟩ I 
_ =
  begin
    inc ⟨⟩ O
  ≡⟨⟩
   ⟨⟩ I
   ∎
  

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc ⟨⟩ I O ≡ ⟨⟩ I I
_ = refl 

_ : inc ⟨⟩ I I ≡ ⟨⟩ I O O 
_ = refl

_ : inc ⟨⟩ I O I I ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc ((to n))

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = (from b) * 2 
from (b I) = suc ((from b) * 2)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : 0 ≡ from (⟨⟩ O)
_ = refl

_ : 1 ≡ from (⟨⟩ I)
_ = refl

_ : 2 ≡ from (⟨⟩ I O)
_ = refl

_ : 3 ≡ from (⟨⟩ I I)
_ = refl

_ : 4 ≡ from (⟨⟩ I O O)
_ = refl



