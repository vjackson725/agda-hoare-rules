{-
  An implementation of Hoare Logic for IMP
-}

module Hoare where

open import Agda.Primitive

open import Data
open import Util

open import IMP
open import SOS

-- Hoare Rules
-- no ⦃ ⦄ brackets because they're reserved :(
data ⟪_⟫_⟪_⟫ {l} : (State → Set l) → Prog → (State → Set l) → Set (lsuc l) where
  SKIP : ∀ {P} → ⟪ P ⟫ skip ⟪ P ⟫
  ASSIGN : ∀ {P} {v : VName} {e : AExp} → ⟪ (λ σ → P (σ [ v ↦ e σ ])) ⟫ v := e ⟪ P ⟫
  SEMI : ∀ {P Q R} {c₁ c₂ : Prog} →
         ⟪ P ⟫ c₁ ⟪ Q ⟫ → ⟪ Q ⟫ c₂ ⟪ R ⟫ →
         ⟪ P ⟫ c₁ >> c₂ ⟪ R ⟫
  COND : ∀ {P Q} {b : BExp} {c₁ c₂ : Prog} →
         ⟪ (λ σ → P σ × So (b σ)) ⟫ c₁ ⟪ Q ⟫ → ⟪ (λ σ → P σ × So (not (b σ))) ⟫ c₂ ⟪ Q ⟫ →
         ⟪ P ⟫ [IF b THEN c₁ ELSE c₂ FI] ⟪ Q ⟫
  WHILE : {P Q : State → Set l} {b : BExp}{c : Prog} →
         ⟪ (λ σ → P σ × So (b σ)) ⟫ c ⟪ P ⟫ →
         (INV : (σ : State) → So (not (b σ)) → P σ → Q σ) →
         ⟪ P ⟫ [WHILE b DO c OD] ⟪ Q ⟫
  WEAKEN : ∀ {P P' Q Q' : State → Set l} {c : Prog} →
         (∀ σ → P σ → P' σ) →
         ⟪ P' ⟫ c ⟪ Q' ⟫ →
         (∀ σ → Q' σ → Q σ) →
         ⟪ P ⟫ c ⟪ Q ⟫ 

-- Hoare Logic is correct for partial correctness on SOS
hoare-sos-partial : ∀ {l} {P Q : State → Set l} (c : Prog) → ⟪ P ⟫ c ⟪ Q ⟫ → ∀ {σ σ'} → P σ → (⟨ c , σ ⟩→ σ') → Q σ'
hoare-sos-partial .skip SKIP P skipSOS = P
hoare-sos-partial .(assign _ _) ASSIGN P assignSOS = P
hoare-sos-partial .(semi _ _) (SEMI h₁ h₂) P (semiSOS s₁ s₂) = hoare-sos-partial _ h₂ (hoare-sos-partial _ h₁ P s₁) s₂
hoare-sos-partial .(cond _ _ _) (COND ht _) P (cond-trueSOS x st) = hoare-sos-partial _ ht (P , so-law-tt-so x) st
hoare-sos-partial .(cond _ _ _) (COND _ hf) P (cond-falseSOS x sf) = hoare-sos-partial _ hf (P , (so-law-ff-so-n x)) sf
hoare-sos-partial .(while _ _) (WHILE h INV) {σ} P (while-endSOS x) = INV σ (so-law-ff-so-n x) P
hoare-sos-partial .(while _ _) (WHILE h INV) {σ} {σ'} P (while-loopSOS x sl sw) = let P' = (hoare-sos-partial _ h (P , so-law-tt-so x) sl)
                                                                               in hoare-sos-partial _ (WHILE h INV) P' sw
hoare-sos-partial c (WEAKEN p' h q') {σ} {σ'} P s = q' σ' (hoare-sos-partial c h (p' σ P) s)

-- TODO: Total correctness is a problem, there's no easy way to represent ∃, because we're constructive
-- (∀ {σ σ'} → P σ → (⟨ c , σ ⟩→ σ') → Q σ') × (∀ {σ} → P σ → (∃ {σ'} → ⟨ c , σ ⟩→ σ' ))
