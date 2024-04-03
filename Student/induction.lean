#check False.rec


--every induciton type come with an induction axiom
#check Bool.rec

/-!
Bool.rec.{u}
  {motive : Bool → Sort u}
  (false :motive false)
  {true : motive true)
  (t : Bool) :
  motive t
-/

example : ∀ (b:Bool),!!b = b :=
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

def fact_0 := 1
def fact_succ :(n:Nat) → (fact_n : Nat) → Nat
--given 10, and the factorial of 10, return the factorial of 11
| n, fact_n => fact_n * (n+1)



#check (Nat.rec fact_0 fact_succ : Nat → Nat)
#reduce (Nat.rec fact_0 fact_succ : Nat → Nat) 5

--(Nat.rec fact_0 fact_succ : Nat → Nat) is the factorial function

--def factorial : Nat → Nat := Nat.rec fact_0 fact_succ --this is not supported yet
--because of Nat.rec


#check List.rec

/-!
List.rec.{u_1, u}
  {α : Type u}
  {motive : List α → Sort u_1}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail → motive (head :: tail))
  (t : List α) : motive t
-/

def list_step {α : Type} : α → List α → Nat → Nat := _

reduce (List.rec 0 list_step _)

def list_empty_len := 0

inductive Tree (α : Type) where
| empty : Tree α
| node (a : α) (l r : Tree α)

#check Tree.rec
