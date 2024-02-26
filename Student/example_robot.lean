/-!
monoid: bineary operator + idendity

monad: enrich functional operator?
allows single operator be applied to n (such as list)?

-/
-----------

/-!Example Robot: Leanba-/

inductive State
|s0
|s120
|s240

inductive Rotation
|r0
|r120
|r240

open State Rotation

def act : Rotation → State → State := _

def add_rotation : Rotation → Rotation → Rotation
| a, r0 => a
| r0, a => a
| r120, r120 => r240
| r120, r240 => r0
| r240, r120 => r0
| r240, r240 => r120

def sub_state : State → State → Rotation
| s0, s0 => r0
| s0, s120 => r240 --s0 - s12
| s0, s240 => r120
| s120, s0 => r120
| s120, s120 => r0
| s120, s240 => r240
| s240, s0 => r240
| s240, s120 => r120
| s240, s240 => r0

instance : Add Rotation := ⟨ add_rotation ⟩

#reduce r120 + r120

instance : AddSemigroup Rotation := ⟨ ⟩
