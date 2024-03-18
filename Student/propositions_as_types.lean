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

#check Classical.em

-- Implication P → Q
-- intro: show that from an *assumed* proof of P, you ca derive a proof of Q
-- elim: *apply* that function to a proof of P to geta  proof of Q
