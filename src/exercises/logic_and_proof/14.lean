/-
Exercises from https://leanprover.github.io/logic_and_proof

Chapter 14. Relations in Lean
-/

/-
Replace the sorry commands in the following proofs to show that we can create
a partial order R'​ out of a strict partial order R.
-/
section ex1

  parameters {A : Type} {R : A → A → Prop}
  parameter (irreflR : irreflexive R)
  parameter (transR : transitive R)

  local infix < := R

  def R' (a b : A) : Prop := R a b ∨ a = b
  local infix ≤ := R'

  theorem reflR' (a : A) : a ≤ a :=
  have a = a, by refl,
  show a ≤ a, from or.inr this

  theorem transR' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c) :
    a ≤ c :=
  h1.elim
    (assume ab,
      (h2.elim
        (assume bc, or.inl (transR ab bc))
        (assume h : b = c, show a ≤ c, from h ▸ h1)))
    (assume h : a = b, show a ≤ c, from h.symm ▸ h2)

  theorem antisymmR' {a b : A} (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b :=
  h1.elim
    (assume ab : a < b,
      h2.elim
        (assume ba : b < a,
          have na : ¬(a < a), from irreflR a,
          have a : a < a, from transR ab ba,
          absurd a na)
        symm)
    id

end ex1

/-
Replace the sorry by a proof.
-/
section ex2
  parameters {A : Type} {R : A → A → Prop}
  parameter (reflR : reflexive R)
  parameter (transR : transitive R)

  include reflR transR

  def S (a b : A) : Prop := R a b ∧ R b a

  example : transitive S :=
  begin
    rw transitive,
    intros a b c sab sbc,
    rw S at *,
    exact ⟨transR sab.left sbc.left, transR sbc.right sab.right⟩
  end
end ex2

/-
Only one of the following two theorems is provable. Figure out which one is
true, and replace the sorry command with a complete proof.
-/
section ex3
  parameters {A : Type} {a b c : A} {R : A → A → Prop}
  parameter (Rab : R a b)
  parameter (Rbc : R b c)
  parameter (nRac : ¬ R a c)

  include Rab Rbc nRac

  -- Prove one of the following two theorems:

  -- theorem R_is_strict_partial_order :
  --   irreflexive R ∧ transitive R :=
  -- sorry

  theorem R_is_not_strict_partial_order :
    ¬(irreflexive R ∧ transitive R) :=
  assume it,
    have transR : transitive R, from it.right,
    have R a c, from transR Rab Rbc,
    absurd this nRac
end ex3

/-
Complete the following proof.
-/
section ex4
  open nat

  example : 1 ≤ 4 :=
  calc 1 ≤ 2 : le_succ 1
     ... ≤ 3 : le_succ 2
     ... ≤ 4 : le_succ 3
end ex4