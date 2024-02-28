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

inductive BobStudiesAtUVaOrMaryStudiesAtUVa
| left (b: BobStudiesAtUVa)
| right (m: MaryStudiesAtUVa)

example : BobStudiesAtUVaOrMaryStudiesAtUVa :=
 BobStudiesAtUVaOrMaryStudiesAtUVa.left b
