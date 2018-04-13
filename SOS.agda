{-
  Structural Operational Semantics (Small Step) for IMP
-}
module SOS where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

open import Util
open import IMP

data ⟨_,_⟩→_ : Prog → State → State → Set where
  skipSOS       : ∀ {σ}              → ⟨ skip , σ ⟩→ σ
  assignSOS     : ∀ {e v σ}          → ⟨ v := e , σ ⟩→ (σ [ v ↦ e σ ])
  semiSOS       : ∀ {σ σ' σ'' c₁ c₂} → ⟨ c₁ , σ ⟩→ σ' → ⟨ c₂ , σ' ⟩→ σ'' → ⟨ c₁ >> c₂ , σ ⟩→ σ''
  cond-trueSOS  : ∀ {b σ σ' c₁ c₂}   → b σ ≡ true   → ⟨ c₁ , σ ⟩→ σ' → ⟨ [IF b THEN c₁ ELSE c₂ FI] , σ ⟩→ σ'
  cond-falseSOS : ∀ {b σ σ' c₁ c₂}   → b σ ≡ false  → ⟨ c₂ , σ ⟩→ σ' → ⟨ [IF b THEN c₁ ELSE c₂ FI] , σ ⟩→ σ'
  while-endSOS  : ∀ {b σ c}          → b σ ≡ false  → ⟨ [WHILE b DO c OD] , σ ⟩→ σ
  while-loopSOS : ∀ {b σ σ' σ'' c}   → b σ ≡ true   → ⟨ c , σ ⟩→ σ' → ⟨ [WHILE b DO c OD] , σ' ⟩→ σ'' → ⟨ [WHILE b DO c OD] , σ ⟩→ σ''
