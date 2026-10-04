import Pspace2ndlevelsmash.Decide

/-!
# Easy cases of the verifier

A verifier receives a guessed certificate and checks it with TAUTOLOGY queries. For a prefix
`∃ȳ ∀z̄` (Σ₂) one assignment to `ȳ` and one query suffice
(`eval_allExists_append_allForall_iff`). This file handles leading universals,
`∀x̄ ∃ȳ ∀z̄` (Π₃): the right `ȳ` may depend on `x̄`, so the certificate is a function
from `x̄` to `ȳ`, checked with one query per value of `x̄`.
-/

namespace Pspace2ndlevelsmash

/-! ## Verifiers that make an explicit list of TAUTOLOGY queries -/

/-- A verifier's queries `(ψ, n)` all pass: each `ψ` is a tautology over `n` variables. -/
def AcceptsAll (queries : List (CNF × Nat)) : Prop := ∀ q ∈ queries, Tautology q.1 q.2

theorem acceptsAll_singleton (ψ : CNF) (n : Nat) : AcceptsAll [(ψ, n)] ↔ Tautology ψ n := by
  simp [AcceptsAll]

theorem tautology_restrict_nil (φ : CNF) (n : Nat) :
    Tautology (φ.restrict []) n ↔ Tautology φ n := by
  rw [tautology_restrict_iff]
  simp [Tautology]

/-- All `∀`: no certificate, and one TAUTOLOGY query on `φ` itself. -/
theorem allForall_one_query {qs : Prefix} (h : AllForall qs) (φ : CNF) :
    Eval qs φ [] ↔ AcceptsAll [(φ, qs.length)] := by
  rw [acceptsAll_singleton, eval_iff_tautology_of_allForall h, tautology_restrict_nil]

/-- One `∃` then all `∀`: the certificate is one bit `b`, and the verifier makes one
TAUTOLOGY query on `φ` with `x₀ := b`. -/
theorem ex_allForall_one_query {rest : Prefix} (h : AllForall rest) (φ : CNF) :
    Eval (.ex :: rest) φ [] ↔ ∃ b : Bool, AcceptsAll [(φ.restrict [b], rest.length)] := by
  simp only [acceptsAll_singleton, eval_ex_allForall_iff h, List.nil_append]

/-! ## `∀x̄ ∃ȳ ∀z̄` -/

/-- `∀x̄ ∃ȳ ∀z̄, φ` is true exactly when every assignment `x` to `x̄` has some assignment `c`
to `ȳ` making the restricted formula `φ(x, c, z̄)` a tautology. -/
theorem eval_all_ex_all_iff {alls₁ exs alls₂ : Prefix} (h₁ : AllForall alls₁)
    (hex : AllExists exs) (h₂ : AllForall alls₂) (φ : CNF) (pre : Assignment) :
    Eval (alls₁ ++ exs ++ alls₂) φ pre ↔
      ∀ x : Assignment, x.length = alls₁.length → ∃ c : Assignment, c.length = exs.length ∧
        Tautology (φ.restrict (pre ++ x ++ c)) alls₂.length := by
  induction alls₁ generalizing pre with
  | nil =>
    rw [List.nil_append, eval_allExists_append_allForall_iff hex h₂]
    refine ⟨fun h x hx => ?_, fun h => by simpa using h [] rfl⟩
    cases x with
    | nil => simpa using h
    | cons _ _ => cases hx
  | cons q alls ih =>
    obtain rfl : q = .all := h₁ q (List.mem_cons_self ..)
    have ih := fun pre => ih (fun q hq => h₁ q (List.mem_cons_of_mem _ hq)) pre
    simp only [List.cons_append, eval_all, List.append_assoc] at ih ⊢
    simp only [ih, List.length_cons]
    constructor
    · intro h x hx
      cases x with
      | nil => cases hx
      | cons b x => simpa using h b x (Nat.succ.inj hx)
    · intro h b x hx
      simpa using h (b :: x) (by simp [hx])

/-- Certificate form: the certificate is a choice function `f` from assignments of `x̄` to
assignments of `ȳ`. The verifier makes one TAUTOLOGY query per `x`, i.e. `2^k` queries for
`k` leading universals, which is polynomial when `k = O(log n)`. -/
theorem eval_all_ex_all_iff_certificate {alls₁ exs alls₂ : Prefix} (h₁ : AllForall alls₁)
    (hex : AllExists exs) (h₂ : AllForall alls₂) (φ : CNF) (pre : Assignment) :
    Eval (alls₁ ++ exs ++ alls₂) φ pre ↔
      ∃ f : Assignment → Assignment, ∀ x : Assignment, x.length = alls₁.length →
        (f x).length = exs.length ∧ Tautology (φ.restrict (pre ++ x ++ f x)) alls₂.length := by
  rw [eval_all_ex_all_iff h₁ hex h₂]
  constructor
  · intro h
    refine ⟨fun x => if hx : x.length = alls₁.length then Classical.choose (h x hx) else [],
      fun x hx => ?_⟩
    simpa [hx] using Classical.choose_spec (h x hx)
  · intro ⟨f, hf⟩ x hx
    exact ⟨f x, hf x hx⟩

/-! ## Why the certificate must depend on `x̄`

`∀x ∃y, (x ∨ ¬y) ∧ (¬x ∨ y)` says `y = x`. It is true, but no single value of `y` works for
both values of `x`, so a certificate that is one fixed assignment to the `∃` variables
cannot verify it. -/

/-- `(x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁)`, i.e. `x₁ = x₀`. -/
def yEqX : CNF := [[⟨0, true⟩, ⟨1, false⟩], [⟨0, false⟩, ⟨1, true⟩]]

theorem yEqX_holds : Eval [.all, .ex] yEqX [] := by decide

theorem yEqX_no_uniform_certificate :
    ¬ ∃ c : Assignment, c.length = 1 ∧
      ∀ x : Assignment, x.length = 1 → Tautology (yEqX.restrict (x ++ c)) 0 := by
  intro ⟨c, hc, h⟩
  match c, hc with
  | [b], _ =>
    have := h [!b] rfl [] rfl
    cases b <;> exact absurd this (by decide)

end Pspace2ndlevelsmash
