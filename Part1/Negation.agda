module Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_ ; s≤s ;z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Isomorphism using (_≃_; extensionality ; _≲_)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
  → ¬ ¬ A
¬¬-intro x = λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀{A B : Set}
  → (A → B)
  → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)

_≢_ : ∀{A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀{n : ℕ} → ¬(n < n)
<-irreflexive (s≤s n<n) = <-irreflexive n<n

tmp : ∀{n m : ℕ} → (suc n) ≡ (suc m) → n ≡ m
tmp refl = refl

tmp1 : ∀{n m : ℕ} → n ≢ m → (suc n) ≢ (suc m)
tmp1 b suc≡ = b (tmp suc≡)

tmp2 : ∀{n m : ℕ} → ¬ (n ≤ m) → ¬ ((suc n) ≤ (suc m))
tmp2 b (s≤s suc≤) = b suc≤

data Trichotomy (a b : ℕ) : Set where
    less : a < b × ¬(a ≡ b) × ¬(b < a) → Trichotomy a b 
    equal : ¬(a < b) × a ≡ b × ¬( b < a) → Trichotomy a b 
    flipped : ¬(a < b) × ¬(a ≡ b) × b < a  → Trichotomy a b 

tricho : ∀(n m : ℕ) → Trichotomy n m
tricho zero zero = equal (<-irreflexive , refl , <-irreflexive)
tricho zero (suc m) = less (s≤s z≤n , (λ ()) , λ ())
tricho (suc n) zero = flipped ((λ ()) , (λ ()) , s≤s z≤n)
tricho (suc n) (suc m) with (tricho n m)
... | less (n<m , ¬n≡m , ¬m<n) = less (s≤s n<m , tmp1 ¬n≡m , tmp2 ¬m<n)
... | equal (¬n<m , n≡m , ¬m<n) = equal (tmp2 ¬n<m , cong suc n≡m , tmp2 ¬m<n)
... | flipped (¬n<m , ¬n≡m , m<n) = flipped (tmp2 ¬n<m , tmp1 ¬n≡m , s≤s m<n)

{-⊎-dual-× : ∀{A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-×  =
  record
    { to = λ{ ¬a⊎b → (λ a → ¬a⊎b (inj₁ a)) , λ b → ¬a⊎b (inj₂ b)}
    ; from = λ{ (¬a , ¬b) (inj₁ a) → ¬a a
              ; (¬a , ¬b) (inj₂ b) → ¬b b}
    ; from∘to = λ{ ¬a⊎b → assimilation ((λ { (¬a , ¬b) (inj₁ a) → ¬a a ; (¬a , ¬b) (inj₂ b) → ¬b b })
                                          ((λ x → ¬a⊎b (inj₁ x)) , (λ x → ¬a⊎b (inj₂ x)))) ¬a⊎b}
    ; to∘from = λ{ (¬a , ¬b) → refl}
    } -}

×-dual-⊎ : ∀{A B : Set} → ¬ (A × B) ≲ (¬ A) ⊎ (¬ B)
×-dual-⊎ =
  record
    { to = λ ¬a×b → inj₁ λ a → ¬a×b {!!}
    ; from = λ{ (inj₁ ¬a) (a , b) → ¬a a
              ; (inj₂ ¬b) (a , b) → ¬b b}
    ; from∘to = {!!}
    }

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-Stable : ∀{A : Set} → Stable (¬ A)
¬-Stable = ¬¬¬-elim

×-Stable : ∀{A B : Set} → Stable A → Stable B → Stable (A × B)
×-Stable sa sb ¬¬a×b = (sa λ {¬a → ¬¬a×b λ {(a , b) → ¬a a}}) , (sb λ {¬b → ¬¬a×b λ { (a , b) → ¬b b}})
                     
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ a → k (inj₁ a)))

record Classical (A B : Set) : Set where
  field
    EM : A ⊎ ¬ A → (¬ ¬ A → A) × (((A → B) → A) → A) × ((A → B) → ¬ A ⊎ B) × (¬ (¬ A × ¬ B) → A ⊎ B)
    DNE : (¬ ¬ A → A) → (A ⊎ ¬ A) × (((A → B) → A) → A) × ((A → B) → ¬ A ⊎ B) × (¬ (¬ A × ¬ B) → A ⊎ B)
    PL : (((A → B) → A) → A) → (A ⊎ ¬ A) × (¬ ¬ A → A) × ((A → B) → ¬ A ⊎ B) × (¬ (¬ A × ¬ B) → A ⊎ B)
    IaD : ((A → B) → ¬ A ⊎ B) → (A ⊎ ¬ A) × (¬ ¬ A → A) × (((A → B) → A) → A) × (¬ (¬ A × ¬ B) → A ⊎ B)
    DM : (¬ (¬ A × ¬ B) → A ⊎ B) → (A ⊎ ¬ A) × (¬ ¬ A → A) × (((A → B) → A) → A) × ((A → B) → ¬ A ⊎ B)
open Classical

class : ∀{A B : Set} → Classical A B
class =
  record
    { EM = λ{ (inj₁ a) → (λ ¬¬a → a) , (λ _ → a) , (λ ab → inj₂ (ab a)) , λ _ → inj₁ a
            ; (inj₂ ¬a) → (λ ¬¬a → ⊥-elim (¬¬a ¬a)) , (λ x → ⊥-elim (¬a (x (λ a → ⊥-elim (¬a a))))) , (λ _ → inj₁ ¬a) , λ ¬¬a×¬b → ⊥-elim (¬¬a×¬b (¬a , λ b → {!!})) }
    ; DNE = λ ¬¬ArA → {!!} , {!!} , {!!} , {!!} 
    ; PL = λ abaa → {!!} , {!!} , {!!} , {!!} 
    ; IaD = λ ab¬a⊎b → {!!} , {!!} , {!!} , {!!} 
    ; DM = λ ¬¬a×¬ba⊎b → {!!} , {!!} , {!!} , {!!} 
    }
