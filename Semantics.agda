
module Semantics where

open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_; _-_ to _-N_; _==_ to _==N_; _<_ to _<N_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Primitive

open import Equality
open import Data
open import Util

VName : Set
VName = Nat

State : Set
State = VName → Nat

AExp : Set
AExp = State → Nat

BExp : Set
BExp = State → Bool

data Com : Set where
  skip : Com
  assign : (v : VName) → (e : AExp) → Com
  semi : (c₁ c₂ : Com) → Com
  cond : (b : BExp) → (c₁ c₂ : Com) → Com
  while : (b : BExp) → (c : Com) → Com

infixl 18 _:=_
pattern _:=_ v e = assign v e

infixl 15 _>>_
pattern _>>_ f g =  semi f g

pattern [IF_THEN_ELSE_FI] b c₁ c₂ = cond b c₁ c₂
pattern [WHILE_DO_OD] b c = while b c

data ⟨_,_⟩→_ : Com → State → State → Set where
  skipSOS       : ∀ {σ}              → ⟨ skip , σ ⟩→ σ
  assignSOS     : ∀ {e v σ}          → ⟨ v := e , σ ⟩→ (σ [ v ↦ e σ ])
  semiSOS       : ∀ {σ σ' σ'' c₁ c₂} → ⟨ c₁ , σ ⟩→ σ' → ⟨ c₂ , σ' ⟩→ σ'' → ⟨ c₁ >> c₂ , σ ⟩→ σ''
  cond-trueSOS  : ∀ {b σ σ' c₁ c₂}   → b σ ≡ true   → ⟨ c₁ , σ ⟩→ σ' → ⟨ [IF b THEN c₁ ELSE c₂ FI] , σ ⟩→ σ'
  cond-falseSOS : ∀ {b σ σ' c₁ c₂}   → b σ ≡ false  → ⟨ c₂ , σ ⟩→ σ' → ⟨ [IF b THEN c₁ ELSE c₂ FI] , σ ⟩→ σ'
  while-endSOS  : ∀ {b σ c}          → b σ ≡ false  → ⟨ [WHILE b DO c OD] , σ ⟩→ σ
  while-loopSOS : ∀ {b σ σ' σ'' c}   → b σ ≡ true   → ⟨ c , σ ⟩→ σ' → ⟨ [WHILE b DO c OD] , σ' ⟩→ σ'' → ⟨ [WHILE b DO c OD] , σ ⟩→ σ''

-- Make an evalation function
module Eval where
  open import Agda.Builtin.Bool

  eval : State → List Com → CoList (State × Com)
  CoList.force (eval σ []) = inl <>
  CoList.force (eval σ (skip ∷ cs))          = inr ((σ , skip) , eval σ cs)
  CoList.force (eval σ (c'@(v := e) ∷ cs))   = inr ((σ , c') , eval (σ [ v ↦ e σ ]) cs)
  CoList.force (eval σ (c'@(c₁ >> c₂) ∷ cs)) = inr ((σ , c') , eval σ (c₁ ∷ c₂ ∷ cs))
  CoList.force (eval σ ([IF b THEN c₁ ELSE c₂ FI] ∷ cs)) with b σ
  CoList.force (eval σ (c'@(cond b c₁ c₂) ∷ cs)) | false = inr ((σ , c') , eval σ (c₂ ∷ cs))
  CoList.force (eval σ (c'@(cond b c₁ c₂) ∷ cs)) | true  = inr ((σ , c') , eval σ (c₁ ∷ cs))
  CoList.force (eval σ ([WHILE b DO c OD] ∷ cs)) with b σ
  CoList.force (eval σ (c'@(while b c) ∷ cs)) | false = inr ((σ , c') , eval σ cs)
  CoList.force (eval σ (c'@(while b c) ∷ cs)) | true  = inr ((σ , c') , eval σ (c ∷ [WHILE b DO c OD] ∷ cs))

module HoareLogic where
  -- Partial Execution Hoare Rules
  -- no ⦃ ⦄ brackets because they're reserved :(
  data P⟪_⟫_⟪_⟫ {l} : (State → Set l) → Com → (State → Set l) → Set (lsuc l) where
    SKIP : ∀ {P} → P⟪ P ⟫ skip ⟪ P ⟫
    ASSIGN : ∀ {P} {v : VName} {e : AExp} → P⟪ (λ σ → P (σ [ v ↦ e σ ])) ⟫ v := e ⟪ P ⟫
    SEMI : ∀ {P Q R} {c₁ c₂ : Com} →
           P⟪ P ⟫ c₁ ⟪ Q ⟫ → P⟪ Q ⟫ c₂ ⟪ R ⟫ →
           P⟪ P ⟫ c₁ >> c₂ ⟪ R ⟫
    COND : ∀ {P Q} {b : BExp} {c₁ c₂ : Com} →
           P⟪ (λ σ → P σ × So (b σ)) ⟫ c₁ ⟪ Q ⟫ → P⟪ (λ σ → P σ × So (not (b σ))) ⟫ c₂ ⟪ Q ⟫ →
           P⟪ P ⟫ [IF b THEN c₁ ELSE c₂ FI] ⟪ Q ⟫
    WHILE : {P Q : State → Set l} {b : BExp}{c : Com} →
           P⟪ (λ σ → P σ × So (b σ)) ⟫ c ⟪ P ⟫ →
           (INV : (σ : State) → So (not (b σ)) → P σ → Q σ) →
           P⟪ P ⟫ [WHILE b DO c OD] ⟪ Q ⟫
    WEAKEN : ∀ {P P' Q Q' : State → Set l} {c : Com} →
           (∀ σ → P σ → P' σ) →
           P⟪ P' ⟫ c ⟪ Q' ⟫ →
           (∀ σ → Q' σ → Q σ) →
           P⟪ P ⟫ c ⟪ Q ⟫ 

-- Let's do a proof

open import Agda.Builtin.Nat renaming (_+_ to _+N_; _-_ to _-N_;  _*_ to _*N_; _<_ to _<N_; _==_ to _==N_)

-- functionally defined factorial, and some laws

fact : Nat → Nat
fact zero = 1
fact (suc n) = (suc n) *N fact n

factorial-law : ∀ {n} → ¬ (0 ≡ n) → n *N (fact (n -N 1)) ≡ fact n
factorial-law {zero} p with p refl
factorial-law {zero} p | ()
factorial-law {suc n} p = refl

nat-<1-01 : ∀ {n} → (1 <N n) ≡ false → (n ≡ 0) + (n ≡ 1)
nat-<1-01 {zero} refl = inl refl
nat-<1-01 {suc zero} p = inr refl
nat-<1-01 {suc (suc n)} ()

-- imperatively defined factorial

fact-imp : Nat → Nat → Com
fact-imp =
    λ A B → (
    B := (λ σ → 1) >>
    [WHILE (λ σ → (1 <N (σ A))) DO
      B := (λ σ → (σ B) *N (σ A)) >>
      A := (λ σ → (σ A) -N 1)
    OD])

-- Hoare proofs

module _ (a b : VName) (abf : (Eq._==_ NatEq a b ≡ false)) where
  open HoareLogic

  fact-fact : (n : Nat) → P⟪ (λ σ → σ a ≡ n) ⟫ fact-imp a b ⟪ (λ σ → σ b ≡ fact n) ⟫
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
      weakQ n σ (p , q) with nat-<1-01 {σ a} (so-law-ff p)
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





-- If we restrict the types to Zero and One, ∧ behaves like conjunction
-- Slightly more general, we only need state indexes
_∧_ : ∀ {lᵢ a b}{I : Set lᵢ} → (I → Set a) → (I → Set b) → (I → Set (a ⊔ b))
(P ∧ Q) i = P i × Q i

module Hoare where
  -- Partial Execution Hoare Rules
  -- no ⦃ ⦄ brackets because they're reserved :(
  P⟪_⟫_⟪_⟫ : ∀ {p q} → (State → Set p) → Com → (State → Set q) → Set (p ⊔ q)
  P⟪ P ⟫ c ⟪ Q ⟫ = ∀ {σ σ'} → P σ → (⟨ c , σ ⟩→ σ') → Q σ'

-- TODO: Total correctness is a problem, there's no easy way to represent ∃, because we're constructive
--  T⟪_⟫_⟪_⟫ : ∀ {p q} → (State → Set p) → Com → (State → Set q) → Set (p ⊔ q)
--  T⟪ P ⟫ c ⟪ Q ⟫ = (∀ {σ σ'} → P σ → (⟨ c , σ ⟩→ σ') → Q σ') * (∀ {σ} → P σ → (∃ {σ'} → ⟨ c , σ ⟩→ σ' ))

  SKIP : ∀ {p} {P : State → Set p} → P⟪ P ⟫ skip ⟪ P ⟫
  SKIP Pσ skipSOS = Pσ

  ASSIGN : ∀ {p} {v : VName}{e : AExp}{P : State → Set p} → P⟪ (λ σ₁ → P (σ₁ [ v ↦ e σ₁ ])) ⟫ v := e ⟪ P ⟫
  ASSIGN Pσ' assignSOS = Pσ'

  SEMI : ∀ {p q r}{e : AExp}{c₁ c₂ : Com}{P : State → Set p}{Q : State → Set q}{R : State → Set r} →
         P⟪ P ⟫ c₁ ⟪ Q ⟫ → P⟪ Q ⟫ c₂ ⟪ R ⟫ →
         P⟪ P ⟫ c₁ >> c₂ ⟪ R ⟫
  SEMI PQ QR Pσ (semiSOS c₁ c₂) = let Qσ'' = PQ Pσ c₁
                                   in QR Qσ'' c₂

  COND : ∀ {p q}{b : BExp}{c₁ c₂ : Com}{P : State → Set p}{Q : State → Set q} →
         P⟪ P ∧ (λ σ → So (b σ)) ⟫ c₁ ⟪ Q ⟫ → P⟪ P ∧ (λ σ → So (not (b σ))) ⟫ c₂ ⟪ Q ⟫ →
         P⟪ P ⟫ [IF b THEN c₁ ELSE c₂ FI] ⟪ Q ⟫
  COND {b = b} [P∧b]Q [P∧¬b]Q Pσ (cond-trueSOS {σ = σ} bσ c) with b σ | [P∧b]Q {σ}
  COND {b = b} [P∧b]Q [P∧¬b]Q Pσ (cond-trueSOS {σ = σ} () c) | false | f
  COND {b = b} [P∧b]Q [P∧¬b]Q Pσ (cond-trueSOS {σ = σ} refl c) | true | f = f (Pσ , <>) c
  COND {b = b} [P∧b]Q [P∧¬b]Q Pσ (cond-falseSOS {σ = σ} bσ c) with b σ | [P∧¬b]Q {σ}
  COND {b = b} [P∧b]Q [P∧¬b]Q Pσ (cond-falseSOS {σ = σ} refl c) | false | f = f (Pσ , <>) c
  COND {b = b} [P∧b]Q [P∧¬b]Q Pσ (cond-falseSOS {σ = σ} () c) | true | f

  WHILE : ∀ {p q}{b : BExp}{c : Com}{P : State → Set p}{Q : State → Set q} →
         P⟪ P ∧ (λ σ → So (b σ)) ⟫ c ⟪ P ⟫ → (∀ σ₁ → (P ∧ (λ σ → So (not (b σ)))) σ₁ → Q σ₁) →
         P⟪ P ⟫ [WHILE b DO c OD] ⟪ Q ⟫
  WHILE {b = b} step PQ Pσ (while-endSOS {σ = σ} bσ) with b σ | PQ σ
  WHILE {b = b} step PQ Pσ (while-endSOS {σ = σ} refl) | false | f = f (Pσ , <>)
  WHILE {b = b} step PQ Pσ (while-endSOS {σ = σ} ()) | true | f
  WHILE {b = b} step PQ Pσ (while-loopSOS {σ = σ} bσ c wc) with b σ | step {σ}
  WHILE {b = b} step PQ Pσ (while-loopSOS {σ = σ} () c wc) | false | f
  WHILE {b = b} step PQ Pσ (while-loopSOS {σ = σ} refl c wc) | true | f = let Pσ'' = f (Pσ , <>) c
                                                                           in WHILE step PQ Pσ'' wc
