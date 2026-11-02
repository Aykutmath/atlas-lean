/-
Parity fixture v3: drift-free Lean-core-only declarations (plain Nat
defs, abbrev over Nat-free universe polymorphism, opaque Nat,
universe levels, Nat literals, let-binding, separate rfl theorems
with no conjunctions, structures, or string computation, whose
elaborations are known to drift between 4.34 and 4.35).

Compiles under both the original 4.34 toolchain and 4.35 with no
Mathlib, so the 4.34 serializer output and the official 4.35
`leanexport` output for the same roots can be judged semantically
equal by the official comparator itself.
-/
universe u

def double : Nat → Nat := fun n => n + n

def ident {α : Type u} (a : α) : α := a

opaque magicNum : Nat := 42

def quad (n : Nat) : Nat :=
  let s := n + n
  s * 2

theorem t_double : double 3 = 3 + 3 := rfl

theorem t_quad : quad 2 = 8 := rfl

theorem t_ident : ident (α := Nat) 5 = 5 := rfl

theorem t_magic : magicNum = magicNum := rfl

theorem anchor_thm : double (quad 1) = 8 := rfl
