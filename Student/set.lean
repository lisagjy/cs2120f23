import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basic
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
  |inl l => _
  |inr r => nomatch r


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
--meaning all elements in the codomain is covered
-- while injective means all elements in the domain is covered

if a function is both injective and surjective

-/

/-!
Set Theory

In lean we will often represnets a set, S, of elements
of type α, as a membership predicate, mem : α → Prop.
There are of course other ways to represent sets.
-/

def a_set : Set Nat := {1, 2, 3}
def b_set : Set Nat := {3, 4, 5}

def a_set' : Set Nat := { n: Nat | n = 1 ∨ n = 2 ∨ n = 3}

example : 1 ∈ a_set := by
  show a_set 1
  unfold a_set
  show 1=1 ∨ 1=2 ∨ 1= 3
  exact Or.inl rfl

example : 3 ∈ a_set ∩ b_set := by
  show 3 ∈ a_set ∧ 3 ∈ b_set
  exact ⟨ Or.inr (Or.inr rfl), Or.inl rfl⟩

--Side note: Consider Russell's Paradox
--Does the set of all set that doesn't contain
--themselves, contain themselves

example : 2 ∈ a_set ∪ b_set := by
  --show 2 ∈ a_set ∨ 2∈ b_set
  exact Or.inl (Or.inr (Or.inl rfl))


--\ is subtract
example : 2 ∈ a_set \ b_set := by
  -- show 2 ∈ a_set ∧ 2 ∉ b_set
  exact ⟨ Or.inr (Or.inl rfl),
    (by
      intro h
      nomatch h)
  ⟩

example : 3 ∉ a_set \ b_set := _

/-!
Compliment of a set
-/
def comp123 : Set Nat := {1,2,3}ᶜ
#reduce comp123

example : 4 ∈ comp123 := by
  intro h
  cases h
  contradiction
  --the hidden h+ variable can't be refer to, so we need to rename it
  rename_i h
  cases h
  contradiction
  -- rename_i h
  -- cases h
  -- ↑this will also work
  contradiction

/-!
Powerset
poweret of n elements, has 2^n elements
-/

/-!
- intersect ∩
- union ∪
- compliment ᶜ
- subset ⊆
- powerset
- set difference \
- set product (cross product)
  --the cardinality of S X T? |SXT| = |S| X |T|
- subset of product set (is a relation)
  -- let r ⊆ S × T be a relation
  -- sometimes we use e instead of r, because it's an edges in the graph
- powerset of the product set of S and T is the set of
-  all relations on S,T
-/

/-!
Properties of Relations

section Relation
-/
#check (@Reflexive) -- Core.lean
#check (@Symmetric)
#check (@Transitive)
#check (@Equivalence) -- Logic.lean

/-!
-/
#reduce Reflexive (@Eq Nat)

--∀ (x: N),x = x
lemma eq_nat_is_refl : Reflexive (@Eq Nat) := by
  unfold Reflexive
  intro x
  exact rfl

lemma eq_nat_is_symm : Symmetric (@Eq Nat) := by
  unfold Symmetric
  intro x y
  intro hxy
  rw [hxy]

lemma eq_nat_is_trans :Transitive (@Eq Nat) := by
  unfold Transitive
  intro x y z
  intro hxy hyz
  rw [hxy]
  rw [hyz]

theorem eq_nat_is_equiv : Equivalence (@Eq Nat) :=
  Equivalence.mk @eq_nat_is_refl @eq_nat_is_symm @eq_nat_is_trans


/-!
Theorem congruence mod n is an equivalence relation
-/

def cong_mod_n : Nat → Nat → Nat → Prop := λ n a b => a%n = b%n

theorem cong_mod_n_equiv' : ∀ n, Equivalence (cong_mod_n n) :=
  by
    intro n
    exact Equivalence.mk _ _ _

lemma cong_mod_n_rfl : ∀ (n:Nat), Reflexive (cong_mod_n n) := by
  intro n
  unfold Reflexive
  intro a
  exact rfl

lemma cong_mod_n_symm : ∀ (n:Nat), Symmetric (cong_mod_n n) := by
  intro n
  unfold Symmetric
  intro x y
  intro hxy
  unfold cong_mod_n
  rw[hxy]


lemma cong_mod_trans :∀ (n:Nat), Transitive (cong_mod_n n) := by
  intro n x y z hxy hyz
  unfold cong_mod_n
  unfold cong_mod_n at hxy hyz
  rw [hxy, hyz]

theorem cong_mod_n_equiv : ∀
