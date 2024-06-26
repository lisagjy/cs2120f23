/-!
Your homework, due before class on Wednesday, is to complete
the definition of the general foldr function, with the reduction
of lists of strings to Boolean values as a test case, true if
every string in a list is of even length, and false otherwise.
Your foldr function must be completely general and not test-case
specific, however the function that we are calling "combine" will
be application/test-case specific. To do the homework, complete
the following definitions by replacing the underscores with your own code.-/

def isEvenLen : String → Bool := λ s => s.length % 2 == 0
def combine : String → Bool → Bool := λ a b => (isEvenLen a) ∧ b

#reduce combine "lifee" true

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

#reduce foldr combine true ["life","and"]


/-!
Notes-/
-- what can go wrong:
-- We can pass a non-identity element

-- rules
-- 1. id is the identiyt element for op
-- 2. op must be associative

/-!
solution:
to prove, for any a in α,
(op a id = a) ∧ (and)
(op id a = a)
Then id is the identity element for op
-/

-- "structure" for defining a data type with just single constructor
-- "mk" is the default name of the constructor
-- can access the attributes using my_monoid.op, my_monoid.id, etc. like OOD
structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a)
(right_id : ∀ (a : α), op a id = a)


def  a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check a_monoid.op
