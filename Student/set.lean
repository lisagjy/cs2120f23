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

Example of Equivelment:
Equal
Congurent with Mod

Anti-symmetric
def antiSym (r : α → α → Prop), ∀ (a b : α),
r a b → r b a → a = b

Asymmetric
def aSym (r : α → α → Prop), ∀ (a b : α),
r a b → ¬ (r b a)
-/
/-!
4/10
More Relations

Partial Order
 - reflexive
 - anti-symmetirc
 - transitive
def isPartialOrder (r : α → α → Prop), (isRefl r) ∧ (antiSym r)
∧ (isTrans r)

Subset
S t := ∀ a , a ∈ s → a ∈ t

Proper Subset
s t := s ⊆ t ∧ ∃ a ∈ t , a ∉ s

Total Order
A total order relation is a partial order in which every
element of the set is comparable with every other element of the set.
 - single_valued r := ∀ x, y, z , r x y → r x z → y = z
 - an answer for every x

many_to_one function
r := ∀ x, y, z, r x z → r

one_to_one injective
r:= single_valued r ∧ ∀ x, y, z, r x z → r y z → x = y

empty relation
example:
inductive Person: Type
|lu
|mary
|jane

def Friends : Person → Person → Prop :=


complete relation
  --Everything is related to everything, including themselves

-/

inductive Person: Type
|lu
|mary
|jane

open Person

def Likes : Person → Person → Prop :=
 λ p1 p2 => (p1 = lu ∧ p2 = mary) ∨ (p1 = mary ∧ p2 = lu)


example : Likes lu mary := Or.inl ⟨rfl, rfl⟩

example : ¬ Likes lu jane :=
λ h: Likes lu jane => by
  cases h with
  |Or.inl l => _
  |Or.inr r => nomatch r


/-!
Powerset of {1,2,3}
{1,2}{2,3}{1,3}
{1}{2}{3}
{}

poset
- Partially Ordered Set

One → many -- not single valued

Set → table → Set
Person → ID
Person: domain of definition
values that have a corresponding vlue in the codomain? : domain
ID: codomain
the values that the domain corresponds to : range

total functon/injective:
every element in the domain of definition have a corresponding value in the codomain
total : F is total iff ∀ a ∈ f.dod, exist b ∈ codomain set, r a b

surjective/onto : f is surjective iff ∀ b ∈ f codomain, ∃ a ∈ f domain, r a b

if a function is both injective and surjective

-/
