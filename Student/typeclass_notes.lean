#check Functor
/-!
If you have type in your structure,
Type universe value

class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)-/

--universe u
inductive Box (α : Type)
| contents (a:α)

def box_map {α β : Type} : (α → β) → Box α → Box β
| f, Box.contents a => Box.contents (f a)
instance : Functor Box := { map := box_map }

instance : Functor Box := ⟨ box_map ⟩
