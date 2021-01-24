module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ allTo× → ⟨ (λ a → proj₁ (allTo× a)) , (λ a → proj₂ (allTo× a)) ⟩
    ; from = λ{ ⟨ left , right ⟩ a → ⟨ left a , right a ⟩}
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ allB) = λ a → inj₁ (allB a)
⊎∀-implies-∀⊎ (inj₂ allC) = λ a → inj₂ (allC a)

{- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
     (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
∀⊎-implies-⊎∀ a = {!The proposition under the 'a needs to match the constructor
                   on the left side and there is no way to know which one it is!} 
-}

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B C : A → Set}  {f g : (∀ (x : A) → B x)} 
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

∀-× : (B : Tri → Set) → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× B =
  record
    { to = λ all → ⟨ all aa , ⟨ all bb , all cc ⟩ ⟩
    ; from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ aa → a
              ; ⟨ a , ⟨ b , c ⟩ ⟩ bb → b
              ; ⟨ a , ⟨ b , c ⟩ ⟩ cc → c }
    ; from∘to = λ all → ∀-extensionality λ tri → {!all tri!}
    ; to∘from = λ y → refl
    }
