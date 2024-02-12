--compact a binary operator and an identity
structure my_monoid' (α : Type) where
(op : α → α → α)
(id : α)

def foldr' {α : Type} : my_monoid' α → List α → α
| m, List.nil => m.id
| m, h::t => m.op h (foldr' m t)

#eval foldr' (my_monoid'.mk Nat.add 0) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk Nat.mul 1) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk String.append "") []

--The Purpose of Monoid
--monoid allows you to take a binary operator, and apply it to any number of arguments
--generalized

def nary_add := foldr' (my_monoid'.mk Nat.add 0)
#eval nary_add [1,2,3,4,5]

def nary_nul := foldr' (my_monoid'.mk Nat.mul 1)

def nary_append := foldr' (my_monoid'.mk String.append "")

/-!
Why does a monoid do?
It extends a binary operator to be a n-ary operator

But so far there is nothing ensuring us to do that-/

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id: ∀ a, op id a = a)
(right_id: ∀ a, op a id = a)
(op_assoc: ∀ a b c, op a (op b c) = op (op a b) c)

def foldr {α : Type} : my_monoid α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr m t)

def nat_add_monoid : my_monoid Nat :=
 my_monoid.mk Nat.add 0 sorry sorry sorry

#eval foldr nat_add_monoid [1,2,3,4,5]

/-!
To prove "for all", assume we have an arbitrary one-/
def nat_add_monoid' : my_monoid Nat :=
⟨
  Nat.add,
  0, --now this cannot be 1 anymore
  λ a => by simp [Nat.add],
  λ a => by simp [Nat.add], --comes from the definition of addition,
  --simp is a function that will go into the def
  --and try to apply it to the condition and goal
  --It will still work if we just say "by simp"
  sorry
⟩
def nat_mul_monoid' : my_monoid Nat :=
⟨
  Nat.mul,
  1,
  λ a => by simp,
  λ a => by simp,
  sorry
⟩

/-!Exercise-/
def nary_mul' : List Nat → Nat := foldr (my_monoid.mk Nat.mul 1 sorry sorry sorry)

#eval nary_mul' [1,2,3,4,5]

/-!
Properties of Pure function programming:
-calling a funciton multiple time, the ouput should alaways be the same-/

/-!
option type
inductive option
| none
| some α
-/

/-!
Another mathematical structure: functor-/
#check (@Option)

def pred : Nat → Option Nat
| 0 => Option.none
| Nat.succ a => a

#reduce pred 3
#reduce pred 0

def option_map {α β : Type} : (α → β) → Option α → Option β
|f, Option.none => Option.none
|f, Option.some a => some (f a)
