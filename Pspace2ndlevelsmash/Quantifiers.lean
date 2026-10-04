/-!
# Quantifier prefixes over a CNF formula

A TQBF instance is a quantifier prefix `Q₁ x₁ … Qₙ xₙ` together with a CNF formula `φ`
over the variables `x₀, x₁, …` (variable `i` is the `i`-th quantifier in the prefix).

Evaluation walks the prefix while building up a partial assignment `pre`; the formula
itself never changes. The proof is organised as a proof by cases on the shape of the prefix.
-/

namespace Pspace2ndlevelsmash

/-! ## Formulas -/

/-- A literal: variable `var`, positive when `pos = true`, negated otherwise. -/
structure Literal where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- An assignment to variables `0, 1, …`, in prefix order. Unassigned variables read `false`. -/
abbrev Assignment := List Bool

def Literal.eval (a : Assignment) (l : Literal) : Bool := a.getD l.var false == l.pos

def Clause.eval (a : Assignment) (c : Clause) : Bool := c.any (Literal.eval a)

def CNF.eval (a : Assignment) (φ : CNF) : Bool := φ.all (Clause.eval a)

/-- Size of a formula: the number of literal occurrences. -/
def CNF.size (φ : CNF) : Nat := (φ.map List.length).sum

/-- Every variable of `φ` is below `n`. A TQBF instance with an `n`-quantifier prefix is
closed when `φ.VarsBelow n`. -/
def CNF.VarsBelow (φ : CNF) (n : Nat) : Prop := ∀ c ∈ φ, ∀ l ∈ c, l.var < n

/-! ## Restriction: plugging a partial assignment into a formula

`φ.restrict pre` fixes variables `0, …, pre.length - 1` to `pre` and renumbers the remaining
variables to start at `0`. A clause containing a true fixed literal is dropped (it is
satisfied), and false fixed literals are deleted from their clause. -/

/-- Restrict a clause; `none` means the clause is already satisfied by `pre`. -/
def Clause.restrict (pre : Assignment) : Clause → Option Clause
  | [] => some []
  | l :: c =>
    if l.var < pre.length then
      if l.eval pre then none else Clause.restrict pre c
    else
      (Clause.restrict pre c).map ({ l with var := l.var - pre.length } :: ·)

def CNF.restrict (pre : Assignment) (φ : CNF) : CNF := φ.filterMap (Clause.restrict pre)

theorem Literal.eval_append_of_lt {l : Literal} {pre : Assignment} (h : l.var < pre.length)
    (a : Assignment) : l.eval (pre ++ a) = l.eval pre := by
  simp [Literal.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem Literal.eval_append_of_ge {l : Literal} {pre : Assignment} (h : pre.length ≤ l.var)
    (a : Assignment) :
    l.eval (pre ++ a) = Literal.eval a { l with var := l.var - pre.length } := by
  simp [Literal.eval, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem Clause.eval_restrict (pre a : Assignment) (c : Clause) :
    (c.restrict pre).elim true (Clause.eval a) = c.eval (pre ++ a) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [Clause.restrict, Clause.eval, List.any_cons] at ih ⊢
    split
    · next hl =>
      rw [Literal.eval_append_of_lt hl]
      split
      · next ht => simp [ht]
      · next ht => simp [ht, ih]
    · next hl =>
      rw [Literal.eval_append_of_ge (Nat.le_of_not_lt hl), ← ih]
      cases Clause.restrict pre c <;> simp [Clause.eval]

/-- Restriction is correct: evaluating `φ.restrict pre` on `a` is evaluating `φ` on `pre ++ a`. -/
theorem CNF.eval_restrict (pre a : Assignment) (φ : CNF) :
    (φ.restrict pre).eval a = φ.eval (pre ++ a) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [CNF.restrict, CNF.eval, List.filterMap_cons, List.all_cons] at ih ⊢
    have hc := Clause.eval_restrict pre a c
    cases h : Clause.restrict pre c with
    | none => simp_all
    | some c' => simp_all [List.all_cons]

theorem Clause.length_restrict_le {pre : Assignment} {c c' : Clause}
    (h : c.restrict pre = some c') : c'.length ≤ c.length := by
  induction c generalizing c' with
  | nil => cases h; exact Nat.le_refl _
  | cons l c ih =>
    simp only [Clause.restrict] at h
    split at h
    · split at h
      · cases h
      · exact Nat.le_succ_of_le (ih h)
    · cases hr : Clause.restrict pre c with
      | none => simp [hr] at h
      | some d =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact Nat.succ_le_succ (ih hr)

/-- Restriction never makes a formula bigger. -/
theorem CNF.size_restrict_le (pre : Assignment) (φ : CNF) : (φ.restrict pre).size ≤ φ.size := by
  induction φ with
  | nil => exact Nat.le_refl _
  | cons c φ ih =>
    simp only [CNF.restrict, CNF.size, List.filterMap_cons, List.map_cons,
      List.sum_cons] at ih ⊢
    cases h : Clause.restrict pre c with
    | none => exact Nat.le_trans ih (Nat.le_add_left _ _)
    | some c' =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (Clause.length_restrict_le h) ih

theorem Clause.varsBelow_restrict {pre : Assignment} {n : Nat} {c c' : Clause}
    (hc : ∀ l ∈ c, l.var < n) (h : c.restrict pre = some c') :
    ∀ l ∈ c', l.var < n - pre.length := by
  induction c generalizing c' with
  | nil => cases h; simp
  | cons l c ih =>
    have hc' : ∀ l ∈ c, l.var < n := fun l hl => hc l (List.mem_cons_of_mem _ hl)
    simp only [Clause.restrict] at h
    split at h
    · split at h
      · cases h
      · exact ih hc' h
    · next hl =>
      cases hr : Clause.restrict pre c with
      | none => simp [hr] at h
      | some d =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        intro l' hl'
        cases hl' with
        | head => have := hc l (List.mem_cons_self ..); dsimp; omega
        | tail _ hl' => exact ih hc' hr l' hl'

/-- If `φ` uses only variables below `n`, then after fixing `pre`, the restricted formula
uses only the `n - pre.length` remaining variables. -/
theorem CNF.varsBelow_restrict {φ : CNF} {n : Nat} (hφ : φ.VarsBelow n) (pre : Assignment) :
    (φ.restrict pre).VarsBelow (n - pre.length) := by
  intro c' hc'
  obtain ⟨c, hc, h⟩ := List.mem_filterMap.mp hc'
  exact Clause.varsBelow_restrict (hφ c hc) h

/-! ## Quantifier prefixes -/

/-- A single quantifier. -/
inductive Quant where
  | all
  | ex
  deriving DecidableEq, Repr

/-- A quantifier prefix, outermost quantifier first. -/
abbrev Prefix := List Quant

/-- Truth of `Q₁ x₁ … Qₙ xₙ, φ` for the prefix `[Q₁, …, Qₙ]`, where the variables before
`x₁` are already fixed to `pre`. The whole instance is `Eval qs φ []`. -/
def Eval : Prefix → CNF → Assignment → Prop
  | [], φ, pre => φ.eval pre = true
  | .all :: qs, φ, pre => ∀ b : Bool, Eval qs φ (pre ++ [b])
  | .ex :: qs, φ, pre => ∃ b : Bool, Eval qs φ (pre ++ [b])

@[simp] theorem eval_nil (φ : CNF) (pre : Assignment) :
    Eval [] φ pre = (φ.eval pre = true) := rfl

@[simp] theorem eval_all (qs : Prefix) (φ : CNF) (pre : Assignment) :
    Eval (.all :: qs) φ pre = ∀ b : Bool, Eval qs φ (pre ++ [b]) := rfl

@[simp] theorem eval_ex (qs : Prefix) (φ : CNF) (pre : Assignment) :
    Eval (.ex :: qs) φ pre = ∃ b : Bool, Eval qs φ (pre ++ [b]) := rfl

/-! ## Cases on the shape of the prefix -/

/-- Case 1: an existential quantifier followed by any number of `∀`/`∃` quantifiers. -/
def ExFirst (qs : Prefix) : Prop := ∃ rest, qs = .ex :: rest

/-- Case 2: a universal quantifier followed by any number of `∀`/`∃` quantifiers. -/
def AllFirst (qs : Prefix) : Prop := ∃ rest, qs = .all :: rest

/-- The cases are exhaustive: a prefix is empty, or starts with `∃`, or starts with `∀`. -/
theorem prefix_cases (qs : Prefix) : qs = [] ∨ ExFirst qs ∨ AllFirst qs := by
  match qs with
  | [] => exact .inl rfl
  | .ex :: rest => exact .inr (.inl ⟨rest, rfl⟩)
  | .all :: rest => exact .inr (.inr ⟨rest, rfl⟩)

/-- Case 1 unfolded: `∃ b` then an arbitrary prefix on the remaining variables. -/
theorem eval_of_exFirst {qs : Prefix} (h : ExFirst qs) (φ : CNF) (pre : Assignment) :
    Eval qs φ pre ↔ ∃ (b : Bool) (rest : Prefix), qs = .ex :: rest ∧
      Eval rest φ (pre ++ [b]) := by
  obtain ⟨rest, rfl⟩ := h
  exact ⟨fun ⟨b, hb⟩ => ⟨b, rest, rfl, hb⟩, fun ⟨b, rest', h, hb⟩ => by
    cases h; exact ⟨b, hb⟩⟩


/-! ## TAUTOLOGY and SAT on concrete formulas -/

/-- TAUTOLOGY: `ψ` holds on every assignment to its `n` variables. -/
def Tautology (ψ : CNF) (n : Nat) : Prop := ∀ a : Assignment, a.length = n → ψ.eval a = true

/-- SAT: `ψ` holds on some assignment to its `n` variables. -/
def Satisfiable (ψ : CNF) (n : Nat) : Prop := ∃ a : Assignment, a.length = n ∧ ψ.eval a = true

theorem tautology_restrict_iff (φ : CNF) (pre : Assignment) (n : Nat) :
    Tautology (φ.restrict pre) n ↔ ∀ a : Assignment, a.length = n → φ.eval (pre ++ a) = true := by
  simp only [Tautology, CNF.eval_restrict]

theorem satisfiable_restrict_iff (φ : CNF) (pre : Assignment) (n : Nat) :
    Satisfiable (φ.restrict pre) n ↔ ∃ a : Assignment, a.length = n ∧ φ.eval (pre ++ a) = true := by
  simp only [Satisfiable, CNF.eval_restrict]

/-! ## All-`∀` prefixes reduce to TAUTOLOGY -/

/-- Every quantifier in the prefix is `∀`. -/
def AllForall (qs : Prefix) : Prop := ∀ q ∈ qs, q = .all

/-- A purely universal prefix is true exactly when the restricted formula is a tautology. -/
theorem eval_iff_tautology_of_allForall {qs : Prefix} (h : AllForall qs) (φ : CNF)
    (pre : Assignment) : Eval qs φ pre ↔ Tautology (φ.restrict pre) qs.length := by
  rw [tautology_restrict_iff]
  induction qs generalizing pre with
  | nil =>
    refine ⟨fun hφ a ha => ?_, fun hφ => by simpa using hφ [] rfl⟩
    cases a with
    | nil => simpa using hφ
    | cons _ _ => cases ha
  | cons q rest ih =>
    obtain rfl : q = .all := h q (List.mem_cons_self ..)
    have ih := fun pre => ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) pre
    simp only [eval_all, ih, List.length_cons]
    constructor
    · intro hφ a ha
      cases a with
      | nil => cases ha
      | cons b a => simpa using hφ b a (Nat.succ.inj ha)
    · intro hφ b a ha
      simpa using hφ (b :: a) (by simp [ha])

/-! ## All-`∃` prefixes reduce to SAT -/

/-- Every quantifier in the prefix is `∃`. -/
def AllExists (qs : Prefix) : Prop := ∀ q ∈ qs, q = .ex

/-- A purely existential prefix is true exactly when the restricted formula is satisfiable. -/
theorem eval_iff_satisfiable_of_allExists {qs : Prefix} (h : AllExists qs) (φ : CNF)
    (pre : Assignment) : Eval qs φ pre ↔ Satisfiable (φ.restrict pre) qs.length := by
  rw [satisfiable_restrict_iff]
  induction qs generalizing pre with
  | nil =>
    refine ⟨fun hφ => ⟨[], rfl, by simpa using hφ⟩, fun ⟨a, ha, hφ⟩ => ?_⟩
    cases a with
    | nil => simpa using hφ
    | cons _ _ => cases ha
  | cons q rest ih =>
    obtain rfl : q = .ex := h q (List.mem_cons_self ..)
    have ih := fun pre => ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) pre
    simp only [eval_ex, ih, List.length_cons]
    constructor
    · intro ⟨b, a, ha, hφ⟩
      exact ⟨b :: a, by simp [ha], by simpa using hφ⟩
    · intro ⟨a, ha, hφ⟩
      cases a with
      | nil => cases ha
      | cons b a => exact ⟨b, a, Nat.succ.inj ha, by simpa using hφ⟩

/-! ## One `∃` followed by `∀`s reduces to TAUTOLOGY under one assignment -/

/-- `∃x₁ ∀x₂ … ∀xₙ, φ` is true exactly when some value `b` for `x₁` makes the restricted
formula `φ(b, x₂, …, xₙ)` a tautology. -/
theorem eval_ex_allForall_iff {rest : Prefix} (h : AllForall rest) (φ : CNF)
    (pre : Assignment) :
    Eval (.ex :: rest) φ pre ↔ ∃ b : Bool, Tautology (φ.restrict (pre ++ [b])) rest.length := by
  simp only [eval_ex, eval_iff_tautology_of_allForall h]

/-! ## A block of `∃`s followed by `∀`s (Σ₂) reduces to TAUTOLOGY under one assignment -/

/-- `∃x₁ … ∃xₖ ∀y₁ … ∀yₘ, φ` is true exactly when some assignment `c` to the `∃` block
makes the restricted formula `φ(c, y₁, …, yₘ)` a tautology. -/
theorem eval_allExists_append_allForall_iff {exs alls : Prefix} (hex : AllExists exs)
    (hall : AllForall alls) (φ : CNF) (pre : Assignment) :
    Eval (exs ++ alls) φ pre ↔ ∃ c : Assignment, c.length = exs.length ∧
      Tautology (φ.restrict (pre ++ c)) alls.length := by
  induction exs generalizing pre with
  | nil =>
    rw [List.nil_append, eval_iff_tautology_of_allForall hall]
    refine ⟨fun hφ => ⟨[], rfl, by simpa using hφ⟩, fun ⟨c, hc, hφ⟩ => ?_⟩
    cases c with
    | nil => simpa using hφ
    | cons _ _ => cases hc
  | cons q exs ih =>
    obtain rfl : q = .ex := hex q (List.mem_cons_self ..)
    have ih := fun pre => ih (fun q hq => hex q (List.mem_cons_of_mem _ hq)) pre
    simp only [List.cons_append, eval_ex, ih, List.length_cons]
    constructor
    · intro ⟨b, c, hc, hφ⟩
      exact ⟨b :: c, by simp [hc], by simpa using hφ⟩
    · intro ⟨c, hc, hφ⟩
      cases c with
      | nil => cases hc
      | cons b c => exact ⟨b, c, Nat.succ.inj hc, by simpa using hφ⟩

/-! ## TQBF instances -/

/-- A closed TQBF instance: a prefix and a CNF formula that only uses the prefix's variables. -/
structure Instance where
  qs : Prefix
  φ : CNF
  closed : φ.VarsBelow qs.length

/-- The instance is true. -/
def Instance.Holds (I : Instance) : Prop := Eval I.qs I.φ []

/-- Every TAUTOLOGY query of the form `I.φ.restrict pre` is a closed formula over the
`I.qs.length - pre.length` remaining variables, and no larger than `I.φ`. -/
theorem Instance.restrict_query (I : Instance) (pre : Assignment) :
    (I.φ.restrict pre).VarsBelow (I.qs.length - pre.length) ∧
      (I.φ.restrict pre).size ≤ I.φ.size :=
  ⟨CNF.varsBelow_restrict I.closed pre, CNF.size_restrict_le pre I.φ⟩

end Pspace2ndlevelsmash
