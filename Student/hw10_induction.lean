#check False.rec


#check Bool.rec

/-
Bool.rec.{u}
  {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) :
  motive t
-/

example : ∀ (b : Bool), !!b = b :=
by
  intros b
  induction b
  repeat { rfl }


#check Nat.rec

/-!
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive (Nat.succ n))
  (t : Nat) :
  motive t
-/


-- answer for base case
def fact_0 := 1

-- given n and answer for n, returns answer for n + 1
def fact_succ : (n : Nat) → (fact_n : Nat) → Nat
| n, fact_n =>  fact_n * (n + 1)

#check (Nat.rec fact_0 fact_succ : Nat → Nat)

#reduce (Nat.rec fact_0 fact_succ : Nat → Nat) 5

#check List.rec

/-!
List.rec.{u_1, u}
  {α : Type u}
  {motive : List α → Sort u_1}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail → motive (head :: tail))
  (t : List α) : motive t
-/

/-! HOMEWORK: complete the following examples -/

-- answer for base case
def len_nil := 0

-- inductive step-up function
def len_cons : (a : Nat) → (l: List Nat) → (len:Nat) → Nat
| _,_,len => len +1

-- test: expect 3
#reduce (List.rec 0 len_cons : List Nat → Nat) [1,2,3]



inductive Tree (α : Type) where
| empty : Tree α
| node (a : α) (l r : Tree α) : Tree α

open Tree

/-
Format the definition of the induction principle for
Tree in this comment block.

Here:

Tree.rec.{u_1, u}
  {α : Type u}
  {motive: Tree α → Sort u_1}
  (empty : motive Tree.empty)
  (node : (a : α) → (l : Tree α)→ (r : Tree α) → motive l → motive r → motive (Tree.node a (Tree.node l) (Tree.node r))
  (t : Tree α):motive t
-/

/-
Define separate base value and step function here,
applying it to the following tree, and show that your
function procuces the right answer.
-/

-- here's a tree of natural numbers with three nodes
def a_tree : Tree Nat :=
  Tree.node
    1
    (Tree.node
      2
      empty
      empty
    )
    (Tree.node
      3
      empty
      empty
    )

-- 1. define answer for base case
def tree_empty := 0

-- 2. define step function
--def len_cons : (a : Nat) → (l: List Nat) → (len:Nat) → Nat

def tree_succ : (a : Nat) → (l : Tree Nat) → (r: Tree Nat) → (l_n : Nat) →  (r_n : Nat) → Nat
| _,_,_,l_n,r_n => l_n + r_n + 1

-- 3. compose them using Tree.rec and apply to a_tree, expecting 3
#reduce (Tree.rec 0 tree_succ : Tree Nat → Nat) a_tree
