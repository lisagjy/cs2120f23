inductive BobStudiesAtUVa
| attendsClasses
| paidTuition

inductive MaryStudiesAtUVa
| attendsClasses
| paidTuition

inductive BobStudiesAtUVaAndMaryStudiesAtUVa
| and (b: BobStudiesAtUVa) (m: MaryStudiesAtUVa)

inductive MarkoStudiesAtUVa

--no proofs meaning this is not true

def neg (α : Type) := α → Empty
example : neg MarkoStudiesAtUVa :=
 λ m : MarkoStudiesAtUVa => nomatch m --no cases to consider

def b : BobStudiesAtUVa := BobStudiesAtUVa.paidTuition
def m : MaryStudiesAtUVa := MaryStudiesAtUVa.paidTuition
example : BobStudiesAtUVaAndMaryStudiesAtUVa :=
 BobStudiesAtUVaAndMaryStudiesAtUVa.and b m

 /-!
 Generalize-/
inductive MyAnd (α β : Type)
| mk (a: α) (b : β)

inductive MyOr (α β : Type) : Type
| inl (a : α)
| inr (b : β)

example : MyAnd BobStudiesAtUVa MaryStudiesAtUVa := MyAnd.mk b m
example : MyOr BobStudiesAtUVa MaryStudiesAtUVa := MyOr.inl b
example : MyOr BobStudiesAtUVa MaryStudiesAtUVa := MyOr.inr m

inductive BobStudiesAtUVaOrMaryStudiesAtUVa
| left (b: BobStudiesAtUVa)
| right (m: MaryStudiesAtUVa)

example : BobStudiesAtUVaOrMaryStudiesAtUVa :=
 BobStudiesAtUVaOrMaryStudiesAtUVa.left b

def MyNot (α : Type) := α → Empty

example : MyNot BobStudiesAtUVa := λ b => _
example : MyNot MarkoStudiesAtUVa := λ m : MarkoStudiesAtUVa => nomatch m

#check @Prod
#check (1,"Hello")

example : Prod BobStudiesAtUVa MaryStudiesAtUVa := Prod.mk b m
example : BobStudiesAtUVa × MaryStudiesAtUVa := (b,m)
example : BobStudiesAtUVa × MaryStudiesAtUVa := ⟨ b,m ⟩

-- *uese* a proof of the conjunction (elimination rules)
example : BobStudiesAtUVa × MaryStudiesAtUVa → BobStudiesAtUVa := λ p => p.1 -- p.fst
example : BobStudiesAtUVa × MaryStudiesAtUVa → MaryStudiesAtUVa := λ p => p.2

#check (@Sum) --or

example : Sum BobStudiesAtUVa MarkoStudiesAtUVa := Sum.inl b
example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa := Sum.inr _ -- no proof,uninhabited type

example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa → BobStudiesAtUVa
| (Sum.inl l) => l
| (Sum.inr r) => nomatch r

example : neg MarkoStudiesAtUVa := λ p : MarkoStudiesAtUVa => nomatch p

example : neg (MarkoStudiesAtUVa × MaryStudiesAtUVa) := λ p => nomatch p.1
/-!
Sort : Sort
Prop : Type
Logical : Value/Computation
Computational Types: Prod
corresponding conjunction of prop : And
-/
--example : BobStudiesAtUVa ∧ MarkoStudiesAtUVa
--we cannot do that because now Bobstudiesatuva is a type, not a prop

inductive B: Prop
| paid
| classes

inductive M: Prop
| paid
| classes

inductive K: Prop

-- And

-- introduction rules --how to construct a pair of proofs
example : And B M := And.intro B.paid M.classes
def b_and_m_true : B ∧ M := And.intro B.paid M.classes
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes
example : B ∧ M := ⟨ B.paid, M.classes⟩

-- elimination rules --how to use a proof that we already have
-- show(P ∨ Q → R) by case analysis on proof of P∨Q
example : B ∧ M → M := λ P => P.right
example : B ∧ M → B := λ P => P.1

theorem foo : B ∧ Not K := ⟨ B.paid, λ k => nomatch k⟩
example : B ∧ ¬K := foo

example : B ∨ K := Or.inl B.paid
example : B ∨ K → B := λ bork => match bork with
| Or.inl b => b
| Or.inr k => nomatch k

/-!
Lean 4 compiles to c
-/

example :
  ∀ (Raining Sprinkling Wet : Prop),
  (Raining ∨ Sprinkling) →
  (Raining → Wet) →
  (Sprinkling → Wet) →
  Wet :=
λ _ _ _ rors rw sw =>
match rors with
| Or.inl r => rw r
| Or.inr s => sw s


-- Not
-- intro: prove ¬P by proving P → False
-- elim: as with any function, elimnation is by apply!

-- intro example
def notK : ¬ K := λ k => nomatch k

-- elim example (law of no contradiction example)
example (P : Prop): ¬ P → P → False :=
λ np p => np p

/-!
The difference between constructive logic and classical logic,
classical logic assumes that a proposition is either true or false, so ¬ ¬ P → P
 --Law of the excluded middle
 --Without this, we cannot do proofs by contradiction
but in constructive logic, ¬ ¬ P implies, there is no proof for ¬ P,
which does  mean we ahve aproof for P, so it's unprovable
-/

example (P : Prop) : ¬ ¬ P → P
| nnp => _ --stuck

example (P : Prop) : (P ∨ ¬ P) → ¬¬P → P
| pornp => match pornp with
  | Or.inl p => λ _ => p
  | Or.inr np => λ nnp => nomatch (nnp np)

--- ∀ (P : Prop), P ∨ ¬P

/-!
Proof utilization (elimination)
-/

example (P Q: Prop) : P ∧ Q → Q ∧ P :=
λ (h : P ∧ Q) => ⟨ h.2, h.1 ⟩ -- And.intro p.right p.left

--different syntax
example (P Q: Prop) : P ∧ Q → Q ∧ P
| And.intro p q => And.intro q p --⟨p, q⟩  => ⟨q, p⟩

example (P Q: Prop) : P ∧ Q → P ∨ Q
|⟨p, q⟩ => Or.inl p

example (P Q : Prop) : P ∨ Q → Q ∨ p
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q

/-!
Proof by negation
-/

/-!
Proof by contradiction
not valid in constructive logic

neither is rule of negation elimination
-/

#check Classical.em
--- ∀ (P : Prop), P ∨ ¬P

-- Implication P → Q
-- intro: show that from an *assumed* proof of P, you ca derive a proof of Q
-- elim: *apply* that function to a proof of P to geta  proof of Q

--rule of negation elimination
example (P : Prop) : (¬¬P → P) :=
match (Classical.em P) with -- a proof of p or not p
| Or.inl p => λ _ => p
| Or.inr np => λ _ => by contradiction

/-!
Implication
-/

def one_not_eq_zero (n : Nat) : n = 1 → n ≠ 0 :=
λ (neq1 : n = 1) =>  λ (neq0 : n = 0) => by
  rw [neq1] at neq0
  cases neq0--elimination rule in equality

/-!
Eqaulity
-/

#check 1 = 0
#check Eq 1 0

/-!
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
-/

#check Eq.refl 1 0

#check 1 = 0
#check Eq 1 0
#check Eq.refl 1

example : 1 = 1 := Eq.refl 1

/-!
#### Predictes
-/

def isEven (n : Nat) : Prop := n % 2 = 0

#check isEven 0
#check isEven 1

#reduce isEven 0
#reduce isEven 1
#reduce isEven 2
#reduce isEven 3
#reduce isEven 4
#reduce isEven 5

/-!
#### For all (∀)

In classical logic, the form of a universally
quantified proposition is ∀ (p : P), Q. This
says that for *any* (p : P) you can pick, Q is
true.
-/

example : ∀ (n : Nat), isEven n := _ -- not true

/-!
#### Introduction
-/

example : ∀ (n : Nat), n = 0 ∨ n ≠ 0 :=
λ n => match n with
| 0 => (Or.inl rfl)
| (_ + 1) => Or.inr (λ h => nomatch h)

/-!
#### Elimination

How do you use a proof of a universal generalization,
∀ (p : P), Q p? Well it's a function of type P → Q p,
taking any value (p : P) to a proof of (Q p): that p
satisfies the predicate Q. To use such a function, you
apply it to a specific, actual parameter value, p, to
obtain a proof of (Q p) for that particular p. This
operation of reducing a proof that everything of a
certain type has some property (Q) to a proof that one
particular value of that type has that property is
called universal specialiation.
-/

variable
  (P : Type)
  (Q : P → Prop)
  (R : Prop)
  (t : P)

#check P
#check Q

#check Q t
#check ∀ (p : P), Q p

/-!
#### Function types as special case of ∀ types
-/

#check ∀ (x : P), R

/-!
What's remarkable now, is that Lean reports back to us that
this proposition, ∀ (_ : P), R, is the type, P → R : Prop!
-/

/-!
#### Exists (∃)
-/

-- general form
example : ∃ (p : P), Q p := _

example : ∃ (n : Nat), isEven n := ⟨ 2 , rfl ⟩
def exists_even_nat : ∃ (n : Nat), isEven n := ⟨ 2 , rfl ⟩

def foo : (∃ (n : Nat), isEven n) → True
| ⟨ n', pf ⟩ => _

example : ∃ (n : Nat), n ≠ 0 := ⟨ 5 , _ ⟩

#check 1 = 0
#check Eq 1 0

#check Eq.refl 1

example : 1 + 1 = 2 := rfl

inductive IsEven : Nat → Prop
| zero_is_even : IsEven 0
| even_plus_2_even : ∀ (n : Nat), IsEven n → IsEven (n + 2)

open IsEven

example : IsEven 0 := zero_is_even
example : IsEven 4 := even_plus_2_even 2 _
