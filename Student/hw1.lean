/-Iterative applying functions-/
def comp4 {α :  Type} : (α → α) → (α → α)
| f => λ a => (f ∘ f ∘ f ∘ f) a

def compn' {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero,f => λ a => a
| (Nat.succ n'), f => λ a => f (compn' n' f a)

#eval (compn' 5 Nat.succ) 0

def compn {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero,_ => λ a => a
| Nat.succ n', f => f ∘ (compn n' f)

#eval (compn 5 Nat.succ) 0

def my_comp {α β γ : Type} : (β → γ) → (α → β) → (α → γ)
| g, f => λ a => (g ∘ f) a --if want to explicitly state the type of a is alpha, it can be written as λ (a: alpha)

def sq (n : Nat) := n * n

#eval (compn 5 sq) 2

/-! Recursive Type: Nat
Defined using inductive-/

#check @List
/-!
inductive List (α : Type u) where
  /-- `[]` is the empty list. -/
  | nil : List α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons (head : α) (tail : List α) : List α
-/

def e : List Nat := List.nil
def e' : List Nat := [] --Just notation

def l1: List Nat := List.cons 1 e
def l1' : List Nat := 1::e --notation
def l1'' : List Nat := [1]

def l2: List Nat := List.cons 0 l1
def l2' : List Nat := 0::l1
def l2'' : List Nat := [0,1]

/- Case analysis with two cases-/
def list_len {α : Type} : List α → Nat
| List.nil => 0
| (List.cons h t) => 1 + list_len t --(List.cons _ t) => 1 + list_len t
