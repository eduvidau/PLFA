module Relations where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; trans)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
      → zero ≤ n

    s≤s : ∀ { m n : ℕ}
      → m ≤ n
      → suc m ≤ suc n

  _ : 2 ≤ 4
  _ = s≤s (s≤s z≤n)

  infix 4 _≤_

  inv-s≤s : ∀ { m n : ℕ}
    → suc m ≤ suc n
    → m ≤ n
  inv-s≤s (s≤s m≤n) = m≤n

  inv-z≤n : ∀ {m : ℕ}
    → m ≤ zero
    → m ≡ zero
  inv-z≤n z≤n = refl

  ≤-refl : ∀ { n : ℕ}
    → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
    → m ≤ p
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s m≤n) (s≤s s) = s≤s (≤-trans m≤n s)

  ≤-antisym : ∀ {m n : ℕ}
    → m ≤ n
    → n ≤ m
    → m ≡ n
  ≤-antisym z≤n z≤n = refl
  ≤-antisym (s≤s m) (s≤s n) = cong suc (≤-antisym m n)

  data Total (m n : ℕ) : Set where

    forward :
      m ≤ n
      ---------
      → Total m n

    flipped :
      n ≤ m
      ---------
      → Total m n

  ≤-total : ∀ ( m n : ℕ) → Total m n
  ≤-total zero n = forward z≤n
  ≤-total (suc m) zero = flipped z≤n
  ≤-total (suc m) (suc n) with ≤-total m n
  ...                        | forward m≤n = forward (s≤s m≤n)
  ...                        | flipped n≤m = flipped (s≤s n≤m)

  +-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
    → n + p ≤ n + q
  +-monoʳ-≤ zero p q p≤q = p≤q
  +-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

  +-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    → m + p ≤ n + p
  +-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

  +-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    → m + p ≤ n + q
  +-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

  *-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
    → n * p ≤ n * q
  *-monoʳ-≤ zero p q p≤q = z≤n
  *-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)
 
  *-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    → m * p ≤ n * p
  *-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n
 
  *-mono-≤ : ∀ (m n p q : ℕ )
    → m ≤ n
    → p ≤ q
    → m * p ≤ n * q
  *-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

  infix 4 _<_

  data _<_ : ℕ → ℕ → Set where

    z<s : ∀ {n : ℕ}
      ------------
      → zero < suc n

    s<s : ∀ {m n : ℕ}
      → m < n
      -------------
      → suc m < suc n

  <-trans : ∀ {m n p : ℕ}
    → m < n
    → n < p
    → m < p
  <-trans z<s (s<s n<p) = z<s
  <-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

  _>_ : ℕ → ℕ → Set
  m > n = n < m
  
  data Trichotomy (m n : ℕ) : Set where

    forward :
      m < n
      ---------
      → Trichotomy m n

    same :
      m ≡ n
      --------
      → Trichotomy m n

    flipped :
      m > n
      ---------
      → Trichotomy m n

  <-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
  <-trichotomy zero zero = same refl
  <-trichotomy zero (suc n) = forward z<s
  <-trichotomy (suc m) zero = flipped z<s
  <-trichotomy (suc m) (suc n) with <-trichotomy m n
  ... | forward m<n = forward (s<s m<n)
  ... | same m≡n = same (cong suc m≡n)
  ... | flipped m>n = flipped (s<s m>n)

  +-monoʳ-< : ∀ (n p q : ℕ)
    → p < q
    → n + p < n + q
  +-monoʳ-< zero p q p<q = p<q
  +-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

  +-monoˡ-< : ∀ (m n p : ℕ)
    → m < n
    → m + p < n + p
  +-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

  +-mono-< : ∀ (m n p q : ℕ)
    → m < n
    → p < q
    → m + p < n + q
  +-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

  --data ≤-iff-< (m n : ℕ) : Set where

  ≤→< : ∀ {m n}
    → suc m ≤ n
    → m < n
  ≤→< (s≤s z≤n) = z<s
  ≤→< (s≤s (s≤s m≤n)) = s<s (≤→< (s≤s m≤n))

  <→≤ : ∀ {m n}
    → m < n
    → suc m ≤ n
  <→≤ z<s = s≤s z≤n
  <→≤ (s<s m<n) = s≤s (<→≤ m<n)

  <-trans-revisited : ∀ {m n p : ℕ}
    → m < n
    → n < p
    → m < p
  <-trans-revisited m<n n<p = ≤→< (≤-trans (≤-trans (<→≤ m<n) (helper)) (<→≤ n<p))
    where  
     helper : ∀ {n : ℕ}
       → n ≤ suc n
     helper {zero} = z≤n
     helper {suc n} = s≤s helper

  data even : ℕ → Set
  data odd : ℕ → Set

  data even where
    zero : even zero
    suc : ∀ {n : ℕ}
      → odd n
      → even (suc n)

  data odd where
    suc : ∀ {n : ℕ}
      → even n
      → odd (suc n)

  e+e≡e : ∀ {m n : ℕ}
    → even m
    → even n
    → even (m + n)

  o+e≡o : ∀{m n : ℕ}
    → odd m
    → even n
    → odd (m + n)

  e+e≡e zero n = n
  e+e≡e (suc om) n = suc (o+e≡o om n)

  o+e≡o (suc em) n = suc (e+e≡e em n)

  o+o≡e : ∀ {m n : ℕ}
    → odd m
    → odd n
    → even (m + n)

  o+o≡e {suc m} {n} (suc em) on rewrite +-comm m n = suc (o+e≡o on em)

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  inc_ : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (b I) = (inc b) O
  inc (b O) = b I

  infixl 6  inc_
  infixl 7  _O _I

  data One : Bin → Set where
    isOne : One (⟨⟩ I)
    zeroNext : ∀ {b} → One b → One (b O)
    oneNext : ∀ {b} → One b → One (b I)
    

  data Can : Bin → Set where
    isZero : Can (⟨⟩ O)
    leadingOne : ∀ {b} → One b → Can b

  inc-one : ∀ {b : Bin} → One b → One (inc b)
  inc-one isOne = zeroNext isOne
  inc-one (zeroNext b) = oneNext b
  inc-one (oneNext b) = zeroNext (inc-one b)
  
  inc-can : ∀ {b : Bin} → Can b → Can (inc b)
  inc-can isZero = leadingOne isOne
  inc-can (leadingOne Ob) = leadingOne (inc-one Ob)

  to : ℕ → Bin
  to zero = ⟨⟩ O 
  to (suc n) = inc ((to n))

  from : Bin → ℕ
  from ⟨⟩ = zero
  from (b O) = (from b) + (from b)
  from (b I) = suc ((from b) + (from b))

  nat-to-can : ∀ (n : ℕ) → Can (to n)
  nat-to-can zero = isZero
  nat-to-can (suc n) = inc-can (nat-to-can n)

  inc->suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
  inc->suc ⟨⟩ = refl
  inc->suc (b O) = refl
  inc->suc (b I) rewrite inc->suc b | +-comm (from b) (suc (from b)) = refl

  suc->inc : ∀ (n : ℕ) → to (suc n) ≡ inc (to n)
  suc->inc n = refl

  _bin-+_ : Bin → Bin → Bin
  b bin-+ i = to ((from b) + (from i))
  {- ⟨⟩ bin-+ n = n
  b bin-+ ⟨⟩ = b
  (b O) bin-+ (n O) = (b bin-+ n) O
  (b O) bin-+ (n I) = (b bin-+ n) I
  (b I) bin-+ (n O) = (b bin-+ n) I
  (b I) bin-+ (n I) = (inc (b bin-+ n)) O -}

  inc-bin-+ʳ : ∀ (b i : Bin) → (inc b) bin-+ i ≡ inc (b bin-+ i) 
  inc-bin-+ʳ ⟨⟩ i = refl
  inc-bin-+ʳ (b O) i = refl
  inc-bin-+ʳ (b I) i rewrite inc->suc (b I) = refl

  inc-bin-+ˡ : ∀ (b i : Bin) → b bin-+ (inc i) ≡ inc (b bin-+ i) 
  inc-bin-+ˡ b i rewrite +-comm (from b) (from (inc i)) | inc-bin-+ʳ i b | +-comm (from i) (from b) = refl
  

  to-bin-+ : ∀ (n : ℕ)
    → to (n + n) ≡ (to n) bin-+ (to n)
  to-bin-+ zero = refl
  to-bin-+ (suc n) rewrite +-comm n (suc n) | to-bin-+ n | sym (inc-bin-+ˡ (to n) (to n)) | sym (inc-bin-+ʳ (to n) (inc (to n)))  = refl

  b-bin-+-b : ∀ (b : Bin) → One b → (b bin-+ b) ≡ b O
  b-bin-+-b ⟨⟩ ()
  b-bin-+-b (b O) (zeroNext o) rewrite to-bin-+ (from b + from b) | b-bin-+-b b o = {!!}
  b-bin-+-b (.⟨⟩ I) isOne = refl
  b-bin-+-b (b I) (oneNext o) rewrite +-comm (from b + from b) (suc (from b + from b)) | b-bin-+-b (b O) (zeroNext o) = refl

{-  b-bin-+-b ⟨⟩ ()
  b-bin-+-b (b O) (zeroNext one) rewrite b-bin-+-b b one = {!!}
  b-bin-+-b (.⟨⟩ I) isOne = refl
  b-bin-+-b (b I) (oneNext one) rewrite b-bin-+-b b one = {!!}
-}
 
  double-lem : ∀ (b : Bin)
    → One b
    → to ((from b) + (from b)) ≡ b O
  double-lem ⟨⟩ ()
  double-lem (b O) (zeroNext o)
    rewrite to-bin-+ (from (b O))
    | double-lem b o
    | b-bin-+-b (b O) (zeroNext o) = refl
  double-lem (.⟨⟩ I) isOne = refl
  double-lem (b I) (oneNext o)
    rewrite +-comm (from b + from b) (suc (from b + from b))
    | suc->inc zero | to-bin-+ (from b + from b)
    | double-lem b o
    | b-bin-+-b (b O) (zeroNext o) = refl
            
  to-from-one : ∀ {b : Bin}
        → One b
        → to (from b) ≡ b
  to-from-one isOne = refl
  to-from-one (zeroNext {b} one) = double-lem b one
  to-from-one (oneNext {b} one) rewrite double-lem b one = refl
     
  to-from-is : ∀ {b : Bin}
    → Can b
    → to (from b) ≡ b
  to-from-is isZero = refl
  to-from-is (leadingOne ob) = to-from-one ob
  
