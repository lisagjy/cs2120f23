example :
∀ (Person : Type)
  (Loves : Person → Person → Prop),
  (∃ (q : Person),∀ (p:Person),Loves p q)
  →  (∀ (p:Person),∃ (q:Person),Loves p q) :=
λ _ _ sel k => match sel with
| ⟨ joe, every_loves_joe ⟩ => ⟨ joe, every_loves_joe k⟩

variable
 (Ball : Type)
 (Heavy : Ball → Prop)
 (Red : Ball → Prop)

example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨ rhb, bisredandheavy.left⟩

example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b ∨ Heavy b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨ rhb, Or.inr bisredandheavy.2⟩


-- example : (¬(∀ (b : Ball), Red b)) →(b : Ball)→ (∃ (b: Ball), ¬ (Red b)) :=
-- λ nabr aball => ⟨_,_ ⟩

example : (∃ (b: Ball), ¬ (Red b)) → (¬(∀ (b : Ball), Red b)) :=
λ nonred =>
match nonred with
  | ⟨ nrb,pfnr ⟩ => λ h =>
    let rb := (h nrb)
    by contradiction
    --False.elim (pfnr rb)
