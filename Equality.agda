
module Equality where

open import Agda.Builtin.Equality

open import Data

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {l l'} {a : Set l} {b : Set l'} {x y : a} (f : a → b) → x ≡ y → f x ≡ f y
cong f refl = refl

_≢_ : ∀ {x} {A : Set x} → A → A → Set x
a ≢ b = (a ≡ b) → Zero

-- barebones version of ≡-reasoning from the std-lib
module ≡-reasoning {a} {A : Set a} where
  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _⟨_⟩≡_
  infix 1 begin_

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin refl = refl

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ refl ⟩ refl = refl

  _⟨_⟩≡_ : (x {y z} : A) → y ≡ x → y ≡ z → x ≡ z
  _ ⟨ refl ⟩≡ refl = refl

  _∎ : ∀ (x : A) → x ≡ x
  _ ∎ = refl
