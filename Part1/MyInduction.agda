module MyInduction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
  (3 + 4) + 5
  ≡⟨⟩
  7 + 5
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)  

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  begin
    (m + suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-swap m n p | +-suc n (m + p) = refl

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

*-suc : ∀ (m n : ℕ) → m * suc n  ≡ m + (m * n)  
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n = cong suc (+-swap n m (m * n))

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p  + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = 
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + m * n * p 
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎
 
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero n = refl
*-comm (suc m) n rewrite *-comm  m n  = sym (*-suc n m) 

zero∸-id : ∀ ( n : ℕ ) → zero ∸ n ≡ zero
zero∸-id zero = refl
zero∸-id (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ ( n + p )
∸-+-assoc zero n p rewrite zero∸-id n | zero∸-id p = sym (zero∸-id (n + p))
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

_^_ : ℕ → ℕ → ℕ
b ^ zero = 1
b ^ suc e = b * (b ^ e)

^-distribˡ-|-* : ∀ ( m n p : ℕ ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p = sym (+-identityʳ (m ^ p))
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p =
  begin
    m * ((m ^ n) * (m ^ p))
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * (m ^ n) * (m ^ p)
  ≡⟨⟩
    (m ^ suc n) * (m ^ p)
  ∎

*-dance : ∀ ( a b c d : ℕ) → a * b * c * d ≡ a * c * (b * d)
*-dance a b c d = 
  begin
    (((a * b) * c) * d)
  ≡⟨ *-assoc (a * b) c d ⟩
    a * b * (c * d)
  ≡⟨ *-assoc a b (c * d)  ⟩
    a * (b * (c * d))
  ≡⟨ cong (a *_) (*-comm b (c * d )) ⟩
   a * ((c * d) * b)
  ≡⟨ sym (*-assoc a (c * d) b) ⟩
    (a * (c * d)) * b
  ≡⟨ *-comm (a * (c * d)) b ⟩
    b * (a * (c * d)) 
  ≡⟨ cong (b *_) (sym (*-assoc a c d)) ⟩
    b * (a * c * d) 
  ≡⟨ *-comm b (a * c * d) ⟩
    (a * c) * d * b
  ≡⟨ *-assoc (a * c) d b ⟩
    (a * c) * (d * b)
  ≡⟨ cong (a * c *_) (*-comm d b) ⟩
    (a * c) * (b * d)
  ≡⟨ sym (*-assoc ((a * c)) b d)  ⟩
    (a * c) * b * d
  ≡⟨ *-assoc (a * c) b d ⟩
    (a * c) * (b * d)
  ∎

^-distribʳ-* : ∀ ( m n p : ℕ ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p =
  begin
    m * n * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩ 
    m * n * (m ^ p) * (n ^ p)
  ≡⟨ *-dance m n (m ^ p) (n ^ p) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) →  (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero =
  begin
    1
  ≡⟨⟩
    (m ^ 0)
  ≡⟨ cong (m ^_) (sym (*-zero n)) ⟩
    (m ^ (n * 0))
  ∎
  
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p =
  begin
  (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-|-* m n (n * p)) ⟩
    (m ^ (n + (n * p)))
  ≡⟨ cong (m ^_) (sym (*-suc n p)) ⟩
  m ^ (n * suc p)
  ∎

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


to : ℕ → Bin
to zero = ⟨⟩ O 
to (suc n) = inc ((to n))

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = double (from b) 
from (b I) = suc (double (from b))

inc->suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc->suc ⟨⟩ = refl
inc->suc (b O) = refl
inc->suc (b I) rewrite inc->suc b = refl

suc->inc : ∀ (n : ℕ) → to (suc n) ≡ inc (to n)
suc->inc n = refl

{-
_ : to (from ⟨⟩) ≡ ⟨⟩ O
_ = {!!}

bin->nat->bin : ∀ (b : Bin) → to (from b) ≡ b
bin->nat->bin ⟨⟩ = {!!}  
bin->nat->bin (b O) with from b
bin->nat->bin (b O) | zero = {!!}
bin->nat->bin (b O) | suc n = {!!}
 {- begin
    to (double (from b))
  ≡⟨ {!!} ⟩
  to (suc (suc (from b)))
  ≡⟨ {!!} ⟩
  to (from b) 
  ≡⟨ {!!} ⟩
    b O
  ∎
-}
bin->nat->bin (b I) = {!!}
-}

nat->bin->nat : ∀ (n : ℕ) → from (to n) ≡ n
nat->bin->nat zero = refl
nat->bin->nat (suc n) =
  begin
    from (inc to n)
  ≡⟨ inc->suc (to n) ⟩
  suc (from (to n))
  ≡⟨ cong suc (nat->bin->nat n) ⟩
    suc n
  ∎

