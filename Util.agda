
module Util where

open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_; _-_ to _-N_; _==_ to _==N_; _<_ to _<N_)
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Data
open import Equality

record Eq {l} (A : Set l) : Set l where
  infix 19 _==_
  field
    _==_ : A → A → Bool
    law-refl : {a : A} → (a == a) ≡ true
    law-sym : {a b : A} → (a == b) ≡ (b == a)

open Eq {{...}}

instance
  NatEq : Eq Nat
  _==_ {{NatEq}} zero zero = true
  _==_ {{NatEq}} zero (suc n) = false
  _==_ {{NatEq}} (suc m) zero = false
  _==_ {{NatEq}} (suc m) (suc n) = m == n
  law-refl {{NatEq}} {zero} = refl
  law-refl {{NatEq}} {suc m} = law-refl {a = m}
  law-sym {{NatEq}} {zero} {zero} = refl
  law-sym {{NatEq}} {zero} {suc b} = refl
  law-sym {{NatEq}} {suc a} {zero} = refl
  law-sym {{NatEq}} {suc a} {suc b} = law-sym {a = a} {b}

  BoolEq : Eq Bool
  _==_ {{BoolEq}} false false = true
  _==_ {{BoolEq}} false true = false
  _==_ {{BoolEq}} true false = false
  _==_ {{BoolEq}} true true = true
  law-refl {{BoolEq}} {false} = refl
  law-refl {{BoolEq}} {true} = refl
  law-sym {{BoolEq}} {false} {false} = refl
  law-sym {{BoolEq}} {false} {true} = refl
  law-sym {{BoolEq}} {true} {false} = refl
  law-sym {{BoolEq}} {true} {true} = refl

_[_↦_] : ∀ {a b} {A : Set a} {B : Set b} {{_ : Eq A}} → (A → B) → A → B → (A → B)
(f [ x ↦ v ]) x' with x' == x
(f [ x ↦ v ]) x' | false = f x'
(f [ x ↦ v ]) x' | true = v

id : ∀ {a}{A : Set a} → A → A
id x = x

natsToList : Nat → List Nat
natsToList zero = []
natsToList (suc m) = m ∷ natsToList m



not : Bool → Bool
not false = true
not true = false

bool-lem : ∀ {b} → not (not b) ≡ b
bool-lem {false} = refl
bool-lem {true} = refl

So : Bool → Set
So false = Zero
So true = One

so-law-tt-so : ∀ {b} → b ≡ true → So b
so-law-tt-so {false} ()
so-law-tt-so {true} refl = <>

so-law-so-tt : ∀ {b} → So b → b ≡ true
so-law-so-tt {false} ()
so-law-so-tt {true} <> = refl

so-law-ff-so-n : ∀ {b} → b ≡ false → So (not b)
so-law-ff-so-n {false} refl = <>
so-law-ff-so-n {true} ()

so-law-so-n-ff : ∀ {b} → So (not b) → b ≡ false
so-law-so-n-ff {false} <> = refl
so-law-so-n-ff {true} ()

so-not-neg-so : ∀ {b} → (So (not b)) → ¬ (So b)
so-not-neg-so {false} <> = id
so-not-neg-so {true} ()


-- Nat laws

suc-inj : ∀ {a} {b} → suc a ≡ suc b → a ≡ b
suc-inj refl = refl

==N-refl : ∀ {a} → (a ==N a) ≡ true
==N-refl {zero} = refl
==N-refl {suc a} = ==N-refl {a}

==N-eq : ∀ {a b} → So (a ==N b) → a ≡ b
==N-eq {zero} {zero} <> = refl
==N-eq {zero} {suc b} ()
==N-eq {suc a} {zero} ()
==N-eq {suc a} {suc b} p = cong suc (==N-eq p)

==N-ff-neq : ∀ {a b} → So (not (a ==N b)) → ¬ (a ≡ b)
==N-ff-neq {zero} {zero} ()
==N-ff-neq {zero} {suc b} <> ()
==N-ff-neq {suc a} {zero} <> ()
==N-ff-neq {suc a} {suc .a} p refl with a ==N a | ==N-refl {a}
==N-ff-neq {suc a} {suc .a} () refl | .true | refl

-- +N laws

+N-assoc : ∀ {a b c} → a +N (b +N c) ≡ a +N b +N c
+N-assoc {zero} {b} {c} = refl
+N-assoc {suc a} {b} {c} rewrite +N-assoc {a} {b} {c} = refl

+N-runit : ∀ {a} → a +N 0 ≡ a
+N-runit {zero} = refl
+N-runit {suc a} = cong suc +N-runit

+N-rsuc : ∀ {a b} → a +N suc b ≡ suc (a +N b)
+N-rsuc {zero} {b} = refl
+N-rsuc {suc a} {b} = cong suc (+N-rsuc {a} {b})

+N-unit-lbound : ∀ {a b} → a +N b ≡ 0 → a ≡ 0
+N-unit-lbound {zero} {b} p = refl
+N-unit-lbound {suc a} {b} ()

+N-unit-rbound : ∀ {a b} → a +N b ≡ 0 → b ≡ 0
+N-unit-rbound {a} {zero} p = refl
+N-unit-rbound {a} {suc b} p with a +N suc b | +N-rsuc {a} {b}
+N-unit-rbound {a} {suc b} () | .(suc (a +N b)) | refl

+N-runit-uniq : ∀ {a b} → a +N b ≡ a → b ≡ 0
+N-runit-uniq {zero} {.0} refl = refl
+N-runit-uniq {suc a} {b} p rewrite +N-rsuc {a} {b} = +N-runit-uniq {a} {b} (suc-inj p)

+N-lunit-uniq : ∀ {a b} → a +N b ≡ b → a ≡ 0
+N-lunit-uniq {zero} {b} refl = refl
+N-lunit-uniq {suc a} {zero} ()
+N-lunit-uniq {suc a} {suc b} p rewrite +N-rsuc {a} {b} = +N-lunit-uniq (suc-inj p)

+N-comm : ∀ {a b} → a +N b ≡ b +N a
+N-comm {zero} {zero} = refl
+N-comm {zero} {suc b} = cong suc (+N-comm {b = b})
+N-comm {suc a} {zero} = cong suc (+N-comm {a})
+N-comm {suc a} {suc b} rewrite +N-rsuc {a} {b} | +N-rsuc {b} {a} | +N-comm {a} {b} = refl

+N-assoc-comm : ∀ {a b c} → a +N b +N c ≡ a +N c +N b
+N-assoc-comm {a} {b} {c} rewrite sym (+N-assoc {a} {b} {c})
                                | sym (+N-assoc {a} {c} {b})
                                | +N-comm {b} {c}
                                = refl

-- *N laws

*N-rabsorb : ∀ {a} → a *N 0 ≡ 0
*N-rabsorb {zero} = refl
*N-rabsorb {suc a} = *N-rabsorb {a}

*N-rabsorb-uniq : ∀ {a b} → ¬ (a ≡ 0) → a *N b ≡ 0 → b ≡ 0
*N-rabsorb-uniq {zero} {b} p refl with p refl
*N-rabsorb-uniq {zero} {b} p refl | ()
*N-rabsorb-uniq {suc a} {zero} p q = refl
*N-rabsorb-uniq {suc a} {suc b} p ()

*N-labsorb-uniq : ∀ {a b} → ¬ (b ≡ 0) → a *N b ≡ 0 → a ≡ 0
*N-labsorb-uniq {zero} {b} p refl = refl
*N-labsorb-uniq {suc a} {zero} p q with a *N zero | *N-rabsorb {a}
*N-labsorb-uniq {suc a} {zero} p q | _ | refl with (p q)
*N-labsorb-uniq {suc a} {zero} p q | _ | refl | ()
*N-labsorb-uniq {suc a} {suc b} p ()

*N-runit : ∀ {a} → a *N 1 ≡ a
*N-runit {zero} = refl
*N-runit {suc a} = cong suc *N-runit

*N-rsuc : ∀ {a b} → a *N suc b ≡ a +N a *N b
*N-rsuc {zero} {b} = refl
*N-rsuc {suc a} {zero} = cong suc (*N-rsuc {a})
*N-rsuc {suc a} {suc b} rewrite +N-rsuc {a} {b +N a *N suc b}
                              | *N-rsuc {a} {suc b}
                              | *N-rsuc {a} {b}
                              | +N-assoc {b} {a} {a +N a *N b}
                              | +N-comm {b} {a}
                              | +N-assoc {a} {b} {a +N a *N b}
                              | +N-assoc {a +N b} {a} {a *N b}
                              = refl

*N-runit-uniq : ∀ {a b} → ¬ (a ≡ 0) → a *N b ≡ a → b ≡ 1
*N-runit-uniq {zero} {b} p refl with p refl
*N-runit-uniq {zero} {b} p refl | ()
*N-runit-uniq {suc a} {zero} p q with a *N 0 | *N-rabsorb {a}
*N-runit-uniq {suc a} {zero} p () | .0 | refl
*N-runit-uniq {suc a} {suc b} p q rewrite *N-rsuc {a} {b}
                                        | +N-assoc {b} {a} {a *N b}
                                        | +N-comm {b} {a}
                                        | sym (+N-assoc {a} {b} {a *N b})
                                        | +N-unit-lbound {b} (+N-runit-uniq (suc-inj q))
                                        = refl

*+N-distribl : ∀ {a b c} → a *N (b +N c) ≡ (a *N b) +N (a *N c)
*+N-distribl {zero} {b} {c} = refl
*+N-distribl {suc a} {b} {c} rewrite *+N-distribl {a} {b} {c}
                                   | +N-assoc {b +N c} {a *N b} {a *N c}
                                   | +N-assoc {b +N (a *N b)} {c} {a *N c}
                                   | +N-assoc-comm {b} {a *N b} {c}
                                   = refl

*+N-distribr : ∀ {a b c} → (a +N b) *N c ≡ (a *N c) +N (b *N c)
*+N-distribr {zero} {b} {c} = refl
*+N-distribr {suc a} {b} {c} rewrite *+N-distribr {a} {b} {c}
                                   | +N-assoc {c} {a *N c} {b *N c}
                                   = refl

*N-assoc : ∀ {a b c} → a *N (b *N c) ≡ a *N b *N c
*N-assoc {zero} {b} {c} = refl
*N-assoc {suc a} {b} {c} rewrite *+N-distribr {b} {a *N b} {c}
                               | *N-assoc {a} {b} {c}
                               = refl

-- Set valued nat comparison

_<_ : Nat → Nat → Set
m < zero = Zero
zero < suc n = One
suc m < suc n = m < n

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans {a} {b} {zero} p ()
<-trans {a} {zero} {suc c} () <>
<-trans {zero} {suc b} {suc c} <> q = <>
<-trans {suc a} {suc b} {suc c} p q = <-trans {a} {b} {c} p q

<-imp-<N : ∀ {a b} → a < b → So (a <N b)
<-imp-<N {a} {zero} ()
<-imp-<N {zero} {suc b} <> = <>
<-imp-<N {suc a} {suc b} p = <-imp-<N {a} {b} p

<Nt-imp-< : ∀ {a b} → So (a <N b) → a < b
<Nt-imp-< {a} {zero} ()
<Nt-imp-< {zero} {suc b} <> = <>
<Nt-imp-< {suc a} {suc b} p = <Nt-imp-< {a} {b} p

<N-trans : ∀ {a b c} → So (a <N b) → So (b <N c) → So (a <N c)
<N-trans {a} {b} {zero} p ()
<N-trans {a} {zero} {suc c} () <>
<N-trans {zero} {suc b} {suc c} <> q = <>
<N-trans {suc a} {suc b} {suc c} p q = <N-trans {a} {b} {c} p q

<N-neq-bound : ∀ {a b} → So (a <N b) → ¬ (a ≡ b)
<N-neq-bound {zero} {zero} () refl
<N-neq-bound {zero} {suc b} <> ()
<N-neq-bound {suc a} {zero} () ()
<N-neq-bound {suc a} {suc b} p q = <N-neq-bound p (suc-inj q)
