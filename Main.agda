
module Main where

open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_; _-_ to _-N_; _==_ to _==N_; _<_ to _<N_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Primitive

open import Equality
open import Data
open import Util

open import IMP
open import Hoare

--
-- Let's do a proof (obligatory factorial example)
--

--
-- functionally defined factorial, and some laws
--

fact : Nat → Nat
fact zero = 1
fact (suc n) = (suc n) *N fact n

--
-- imperatively defined factorial
--

fact-imp : Nat → Nat → Prog
fact-imp =
    λ A B → (
    B := (λ σ → 1) >>
    [WHILE (λ σ → (1 <N (σ A))) DO
      B := (λ σ → (σ B) *N (σ A)) >>
      A := (λ σ → (σ A) -N 1)
    OD])

--
-- Hoare proofs
--

-- some laws used in the proof
factorial-law : ∀ {n} → ¬ (0 ≡ n) → n *N (fact (n -N 1)) ≡ fact n
factorial-law {zero} p with p refl
factorial-law {zero} p | ()
factorial-law {suc n} p = refl

nat-<1-01 : ∀ {n} → (1 <N n) ≡ false → (n ≡ 0) + (n ≡ 1)
nat-<1-01 {zero} refl = inl refl
nat-<1-01 {suc zero} p = inr refl
nat-<1-01 {suc (suc n)} ()


module _ (a b : VName) (abf : (Eq._==_ NatEq a b ≡ false)) where
  open Hoare

  -- Proof that factorial (in IMP) implements factorial (in Agda) correctly
  fact-fact : (n : Nat) → ⟪ (λ σ → σ a ≡ n) ⟫ fact-imp a b ⟪ (λ σ → σ b ≡ fact n) ⟫
  fact-fact n = WEAKEN
                  (weakP n)
                  (SEMI
                    ASSIGN
                    (WHILE
                      (WEAKEN
                        (weak-loopP n)
                        (SEMI ASSIGN ASSIGN)
                        λ σ → id)
                      (loop-inv n)))
                  (weakQ n)
    where
      weakP : (n : Nat) (σ : State) → σ a ≡ n → ((σ [ b ↦ 1 ]) b) *N fact ((σ [ b ↦ 1 ]) a) ≡ fact n
      weakP n σ p with Eq.law-refl NatEq {b}
      weakP n σ p | bb rewrite abf | bb | +N-runit {fact (σ a)} | p = refl
      
      weakQ : (n : Nat) (σ : State) → (So (not (1 <N σ a))) × (σ b *N fact (σ a) ≡ fact n) → σ b ≡ fact n
      weakQ n σ (p , q) with nat-<1-01 {σ a} (so-law-so-n-ff p)
      weakQ n σ (p , q) | inl x rewrite x | *N-runit {σ b} = q
      weakQ n σ (p , q) | inr x rewrite x | *N-runit {σ b} = q

      weak-loopP : (n : Nat) (σ : State) →
               (σ b *N fact (σ a) ≡ fact n) × So (1 <N σ a) →
               ((σ [ b ↦ σ b *N σ a ]) [ a ↦ (σ [ b ↦ σ b *N σ a ]) a -N 1 ]) b
                 *N
               fact (((σ [ b ↦ σ b *N σ a ]) [ a ↦ (σ [ b ↦ σ b *N σ a ]) a -N 1 ]) a)
               ≡ fact n
      weak-loopP n σ (p , q) rewrite Eq.law-refl NatEq {a}
                                 | Eq.law-sym NatEq {b} {a}
                                 | abf
                                 | Eq.law-refl NatEq {b}
                                 | sym (*N-assoc {σ b} {σ a} {fact (σ a -N 1)})
                                 | factorial-law {σ a} (<N-neq-bound (<N-trans {0} {1} {σ a} <> q))
                                 = p

      loop-inv : (n : Nat) (σ : State) →
             So (not (1 <N σ a)) →
             σ b *N fact (σ a) ≡ fact (n) →
             (So (not (1 <N σ a))) × (σ b *N fact (σ a) ≡ fact n)
      loop-inv n σ p q = p , q
