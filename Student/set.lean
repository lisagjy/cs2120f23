/-!
set
isEven: Nat→ Prop := λ n => n % 2 = 0
evens := {n: Nat | isEven n}

relations
lesseq: Nat → Nat → Prop
2 ≤ 3
3 ≤ 2

Preoperties of Binary Relations on a set α

Symmetrical Relation
∀ (a b :α), r a b → r b a

Binary relation on a arbitrary type
α → α → Prop

What is the type of the property of a binary relation?
-- predicate

def isSym (r : α → α → Prop):
___ --what is the type of this? a proposition? Type: Relation → Prop
:= ∀ (a b :α), r a b → r b a

what is the type of isSym? (a property of a relation)
-- predicate?
-- (α → α → Prop) → Prop
-- Relations → Prop


Reflexive
(an example would be equality, but not just equality; related to itself)
def isRefl := ∀ (r : α → α → Prop):
 ∀ (a : α), r a a

Transitive
def isTrans (r : α → α → Prop),
∀ (a b c : α), r a b → r b c → r a c --equivelent to r a b ∧ r b c → r a c
--but using → requires no decomposition

Equivelence
def isEquiv (r : α → α → Prop), (isSym r) ∧ (isRefl r)
∧ (isTrans r)

Anti-symmetric
def antiSym (r : α → α → Prop), ∀ (a b : α),
r a b → r b a → a = b

Asymmetric
def aSym (r : α → α → Prop), ∀ (a b : α),
r a b → ¬ (r b a)
-/
