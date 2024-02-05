/-(1) Write a function called add that takes two natural numbers, a and b,
and returns their sum, a + b. Don't just look up the answer. Figure it out
on your own. Hint: do case analysis on the second argument (a Nat can be
either Nat.zero or (Nat.succ n') and use the fact that n + (1 + m) = 1 +
(n + m).-/

def add : Nat → Nat → Nat
| Nat.zero, a => a
| (Nat.succ n'), a => (Nat.succ (add n' a))

#eval add 2 4
#check Nat.mul

def mul : Nat → Nat → Nat
| Nat.zero, _ => 0
| Nat.succ n', m => add (mul n' m) m

#eval Nat.mul 5 4
#eval mul 5 4

def exp : Nat → Nat → Nat
| n, 0 => 1
| n, Nat.succ m' => mul n (exp n m')

#eval exp 2 4
#eval exp 8 0

/-(2) Write a function called append, polymorphic in a type, T, that takes
two lists values, n and m of type List T and that returns the result of
appending the two lists. For example, append [1,2,3] [4,5,6], should return
[1,2,3,4,5,6]. Hint: It's very much list Nat addition.-/

def append {T : Type} : List T → List T → List T
| List.nil, a => a
| List.cons h t, a => List.cons h (append t a)

#eval append [1,2,3] [4,5,6]

#check (@Empty)
--inductive Empty : Type

#check Bool
#check Unit
