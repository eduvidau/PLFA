module Equality where

  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  infix 4 _≡_

  sym : ∀ {A : Set} {x y : A}
    → x ≡ y
    → y ≡ x
  sym refl = refl

  trans : ∀ {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
  trans refl refl = refl

  cong : ∀ {A B : Set} (f : A → B) {x y : A}
    → x ≡ y
    → f x ≡ f y
  cong f refl = refl

  cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
    → u ≡ x
    → v ≡ y
    → f u v ≡ f x y
  cong₂ f refl refl = refl

  cong-app : ∀ {A B : Set} {f g : A → B}
    → f ≡ g
    → ∀ (x : A) → f x ≡ g x
  cong-app refl x = refl

  subs : ∀ {A : Set} {x y : A} (P : A → Set)
    → x ≡ y
    → P x → P y
  subs P refl px = px

  module ≡-Reasoning {A : Set} where

    infix 1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix 3 _∎

    begin_ : ∀ {x y : A}
      → x ≡ y
      → x ≡ y
    begin x≡y = x≡y

    _≡⟨⟩_ : ∀ (x : A) {y z : A}
      → x ≡ y
      → x ≡ y
    x ≡⟨⟩ x≡y = x≡y

    _≡⟨_⟩_ : ∀ (x : A) {y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
    x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    _∎ : ∀ (x : A)
      → x ≡ x
    x ∎ = refl

  open ≡-Reasoning

  trans' : ∀ {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    → x ≡ z
  trans' {A} {x} {y} {z} x≡y y≡z =
    begin
      x
    ≡⟨ x≡y ⟩
      y
    ≡⟨ y≡z ⟩
      z
    ∎

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)

  postulate
    +-identity : ∀ (m : ℕ) → m + zero ≡ m
    +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

  +-comm : ∀ ( m n : ℕ) → m + n ≡ n + m
  +-comm m zero =
    begin
      m + zero
    ≡⟨ +-identity m ⟩
      m
    ≡⟨ refl ⟩
      zero + m
    ∎
  +-comm m (suc n) =
    begin
      (m + suc n)
    ≡⟨ +-suc m n ⟩
      suc (m + n)
    ≡⟨ cong suc ((+-comm m n)) ⟩
      suc (n + m)
    ≡⟨ refl ⟩
      suc n + m
    ∎

  data _≤_  : ∀ (n m : ℕ) → Set where
    z≤n : ∀ {n : ℕ}
      → zero ≤ n

    s≤s : ∀ {m n : ℕ}
      → m ≤ n
      → suc m ≤ suc n

  infix 5 _≤_

  ≤-refl : ∀ {n}
    → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl
  
  ≤-trans : ∀ {x y z : ℕ}
    → x ≤ y
    → y ≤ z
    → x ≤ z
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)
  

  module ≤-Reasoning  where

    infix 1 ≤begin_
    infixr 2 _≤⟨⟩_ _≤⟨_⟩_
    infix 3 _∎≤

    ≤begin_ : ∀ {x y : ℕ}
      → x ≤ y
      → x ≤ y
    ≤begin x≤y = x≤y

    _≤⟨⟩_ : ∀ (x : ℕ) {y z : ℕ}
      → x ≤ y
      → x ≤ y
    x ≤⟨⟩ x≤y = x≤y

    _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
      → x ≤ y
      → y ≤ z
      → x ≤ z
    x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

    _∎≤ : ∀ (x : ℕ)
      → x ≤ x
    x ∎≤ = ≤-refl

  open ≤-Reasoning

  foo : ∀ (m : ℕ)
    → m + zero ≤ m
  foo m = subs (λ x → x ≤ m) (sym (+-identity m)) ≤-refl

  bar : ∀ (m : ℕ)
    → m ≤ m + zero
  bar m = subs (λ x → m ≤ x) (sym (+-identity m)) ≤-refl

  +-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    → m + p ≤ n + p
  +-monoˡ-≤ m n zero m≤n =
    ≤begin
      (m + zero)
    ≤⟨ subs (λ x → x ≤ m) (sym (+-identity m)) ≤-refl ⟩ -- ≤⟨ foo m ⟩
      m
    ≤⟨ m≤n ⟩
      n
    ≤⟨ subs (λ x → n ≤ x) (sym (+-identity n)) ≤-refl ⟩ -- ≤⟨ bar n ⟩
      (n + zero)
    ∎≤
  +-monoˡ-≤ m n (suc p) m≤n = 
    ≤begin
      m + (suc p)
    ≤⟨ subs (λ x → x ≤ (suc (m + p))) (sym (trans (+-comm m (suc p)) (cong suc (+-comm p m)))) ≤-refl ⟩
      suc (m + p)
    ≤⟨ s≤s (+-monoˡ-≤ m n p m≤n) ⟩
      suc (n + p)
    ≤⟨ subs (λ x → (suc (n + p)) ≤ x) (trans (cong suc (+-comm n p)) (+-comm (suc p) n)) ≤-refl ⟩
      n + (suc p)
    ∎≤
  
  +-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
    → n + p ≤ n + q
  +-monoʳ-≤ zero p q p≤q =
    ≤begin
      zero + p
    ≤⟨ ≤-refl ⟩
      p
    ≤⟨ p≤q ⟩
      q
    ≤⟨ ≤-refl ⟩
      zero + q
    ∎≤
  +-monoʳ-≤ (suc n) p q p≤q = 
    ≤begin
      ((suc n) + p)
    ≤⟨ ≤-refl ⟩
      suc (n + p)
    ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
      suc (n + q)
    ≤⟨ ≤-refl ⟩
      ((suc n) + q)
    ∎≤
    
  +-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    → m + p ≤ n + q
  +-mono-≤ m n p q m≤n p≤q = 
    ≤begin
      (m + p)
    ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
      (n + p)
    ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
      (n + q)
    ∎≤

  data even : ℕ → Set
  data odd  : ℕ → Set

  data even where

    even-zero : even zero

    even-suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

  data odd where
    odd-suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

  {-# BUILTIN EQUALITY _≡_ #-}

  even-com : ∀ (m n : ℕ)
    → even (m + n)
    → even (n + m)
  even-com m n ev rewrite +-comm n m = ev

  even-comm' : ∀ (m n : ℕ)
    → even (m + n)
    → even (n + m)
  even-comm' m n env with m + n    | +-comm m n
  ...                   | .(n + m) | refl = env

  even-comm″ : ∀ (m n : ℕ)
    → even (m + n)
      ------------
    → even (n + m)
  even-comm″ m n  = subs even (+-comm m n) 

  _≐_ : ∀ {A : Set} (x y : A) → Set₁
  _≐_ {A} x y = ∀ (P : A → Set) → P x → P y

  refl-≐ : ∀ {A : Set} {x : A}
    → x ≐ x
  refl-≐ P Px = Px

  trans-≐ : ∀ {A : Set} {x y z : A}
    → x ≐ y
    → y ≐ z
    → x ≐ z
  trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

  sym-≐ : ∀ {A : Set} {x y : A}
    → x ≐ y
    → y ≐ x
  sym-≐ {A} {x} {y} x≐y P = Qy
    where
      Q : A → Set
      Q z = P z → P x
      Qx : Q x
      Qx = refl-≐ P
      Qy : Q y
      Qy = x≐y Q Qx

  ≡-implies-≐ : ∀ {A : Set} {x y : A}
    → x ≡ y
    → x ≐ y
  ≡-implies-≐ x≡y  P = subs P x≡y

  ≐-implies-≡ : ∀ {A : Set} {x y : A}
    → x ≐ y
    → x ≡ y
  ≐-implies-≡ {A} {x} {y} x≐y = Qy
    where
      Q : A → Set
      Q z = x ≡ z
      Qx : Q x
      Qx = refl
      Qy : Q y
      Qy = x≐y Q Qx

  open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

  data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
    refl' : x ≡' x

  sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
    → x ≡' y
    → y ≡' x
  sym' refl' = refl'

  _≐'_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
  _≐'_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

  _∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
    → (B → C) → (A → B) → A → C
  (g ∘ f) x  =  g (f x)
