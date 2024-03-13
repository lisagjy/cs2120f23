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

example : And B M := And.intro B.paid M.classes
def b_and_m_true : B ∧ M := And.intro B.paid M.classes
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes
example : B ∧ M := ⟨ B.paid, M.classes⟩

example : B ∧ M → M := λ P => P.right
example : B ∧ M → B := λ P => P.1

theorem foo : B ∧ Not K := ⟨ B.paid, λ k => nomatch k⟩
example : B ∧ ¬K := foo

example : B ∨ K := Or.inl B.paid
example : B ∨ K → B := λ bork => match bork with
| Or.inl b => b
| Or.inr k => nomatch k
