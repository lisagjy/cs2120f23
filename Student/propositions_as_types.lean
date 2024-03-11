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
