import Pspace2ndlevelsmash.EasyCases

/-!
# Pattern certificates need exponentially many queries

A *pattern certificate* for `∀x₁ … ∀xₖ ∃y₁ … ∃yₖ, φ` is a list of patterns. Each pattern
fixes the `∃` variables `ȳ` and fixes each `∀` variable `xᵢ` or leaves it as `*`. The
verifier makes one TAUTOLOGY query per pattern (φ with the fixed positions plugged in must
hold for every value of the `*` positions) and checks that the patterns cover every `x̄`.

For the copy formula `(x₁ ↔ y₁) ∧ … ∧ (xₖ ↔ yₖ)`, which has `2k` clauses and is true, every
such certificate has at least `2^k` patterns: a valid pattern cannot leave any `xᵢ` as `*`,
so it covers only one `x̄`.

This is a lower bound for this one verifier design, not for verifiers in general: a
certificate that gives `yᵢ` as a function of `x̄` (here `yᵢ := xᵢ`) needs one query.
-/

namespace Pspace2ndlevelsmash

/-! ## The copy formula -/

/-- `(x₀ ↔ y₀) ∧ … ∧ (xₖ₋₁ ↔ yₖ₋₁)` with `xᵢ` as variable `i` and `yᵢ` as variable `k + i`. -/
def copyCNF (k : Nat) : CNF :=
  (List.range k).flatMap fun i => [[⟨i, true⟩, ⟨k + i, false⟩], [⟨i, false⟩, ⟨k + i, true⟩]]

/-- The copy formula holds when `ȳ` is a copy of `x̄`. -/
theorem copyCNF_eval_self (x : Assignment) : (copyCNF x.length).eval (x ++ x) = true := by
  simp only [CNF.eval, List.all_eq_true]
  intro c hc
  simp only [copyCNF, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at hc
  obtain ⟨i, hi, rfl | rfl⟩ := hc <;>
    simp [Clause.eval, Literal.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
      hi] <;>
    cases x[i] <;> rfl

/-- The copy formula holds only when `ȳ` is a copy of `x̄`. -/
theorem copyCNF_eval_eq {x ys : Assignment} (hy : ys.length = x.length)
    (h : (copyCNF x.length).eval (x ++ ys) = true) : x = ys := by
  simp only [CNF.eval, List.all_eq_true] at h
  apply List.ext_getElem hy.symm
  intro i hx hys
  have mem : ∀ c, c = [⟨i, true⟩, ⟨x.length + i, false⟩] ∨
      c = [⟨i, false⟩, ⟨x.length + i, true⟩] → c ∈ copyCNF x.length := by
    intro c hc
    simp only [copyCNF, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
      or_false]
    exact ⟨i, hx, hc⟩
  have h₁ := h _ (mem _ (.inl rfl))
  have h₂ := h _ (mem _ (.inr rfl))
  simp [Clause.eval, Literal.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left hx,
    hx, hys] at h₁ h₂
  revert h₁ h₂
  cases x[i] <;> cases ys[i] <;> simp

/-- The copy instance `∀x̄ ∃ȳ, x̄ = ȳ` is true. -/
theorem copy_holds (k : Nat) :
    Eval (List.replicate k .all ++ List.replicate k .ex) (copyCNF k) [] := by
  have h := eval_all_ex_all_iff (alls₁ := List.replicate k .all)
    (exs := List.replicate k .ex) (alls₂ := [])
    (fun q hq => (List.mem_replicate.mp hq).2) (fun q hq => (List.mem_replicate.mp hq).2)
    (fun _ h => nomatch h) (copyCNF k) []
  rw [List.append_nil] at h
  rw [h]
  intro x hx
  simp only [List.length_replicate] at hx
  refine ⟨x, by simp [hx], ?_⟩
  rw [tautology_restrict_iff]
  intro a ha
  cases a with
  | nil => subst hx; simpa using copyCNF_eval_self x
  | cons _ _ => cases ha

/-! ## Counting -/

/-- The tails of the lists in `L` that start with `b`. -/
def tailsWith (b : Bool) : List Assignment → List Assignment
  | [] => []
  | [] :: L => tailsWith b L
  | (b' :: t) :: L => if b' = b then t :: tailsWith b L else tailsWith b L

theorem mem_tailsWith {b : Bool} {t : Assignment} {L : List Assignment} (h : b :: t ∈ L) :
    t ∈ tailsWith b L := by
  induction L with
  | nil => cases h
  | cons l L ih =>
    cases List.mem_cons.mp h with
    | inl h => subst h; simp [tailsWith]
    | inr hL =>
      have := ih hL
      match l with
      | [] => exact this
      | b' :: t' =>
        simp only [tailsWith]
        split
        · exact List.mem_cons_of_mem _ this
        · exact this

theorem length_tailsWith (L : List Assignment) :
    (tailsWith false L).length + (tailsWith true L).length ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons l L ih =>
    match l with
    | [] => simp only [tailsWith, List.length_cons]; omega
    | b :: t => cases b <;> simp [tailsWith] <;> omega

/-- A list containing every length-`k` assignment has at least `2^k` entries. -/
theorem pow_le_length_of_covers {k : Nat} {L : List Assignment}
    (h : ∀ a : Assignment, a.length = k → a ∈ L) : 2 ^ k ≤ L.length := by
  induction k generalizing L with
  | zero => exact List.length_pos_of_mem (h [] rfl)
  | succ k ih =>
    have h₀ := ih fun t ht => mem_tailsWith (h (false :: t) (by simp [ht]))
    have h₁ := ih fun t ht => mem_tailsWith (h (true :: t) (by simp [ht]))
    have := length_tailsWith L
    rw [Nat.pow_succ]
    omega

/-! ## Pattern certificates -/

/-- A pattern: each `∀` variable fixed or `*` (`none`), and a fixed assignment to the `∃`
variables. -/
structure Pattern where
  xs : List (Option Bool)
  ys : Assignment

/-- `x` is one of the assignments covered by the pattern. -/
def Pattern.Matches (p : Pattern) (x : Assignment) : Prop :=
  p.xs.length = x.length ∧ ∀ (i : Nat) (b : Bool), p.xs[i]? = some (some b) → x[i]? = some b

/-- The pattern passes its TAUTOLOGY query: `φ` holds on every covered `x` with `ȳ := p.ys`. -/
def Pattern.Valid (φ : CNF) (p : Pattern) : Prop :=
  ∀ x : Assignment, p.Matches x → φ.eval (x ++ p.ys) = true

/-- Any pattern certificate for the copy instance with `k` universals has at least `2^k`
patterns, so the verifier makes at least `2^k` TAUTOLOGY queries. -/
theorem pattern_certificate_lower_bound (k : Nat) (cert : List Pattern)
    (hys : ∀ p ∈ cert, p.ys.length = k)
    (hvalid : ∀ p ∈ cert, p.Valid (copyCNF k))
    (hcover : ∀ x : Assignment, x.length = k → ∃ p ∈ cert, p.Matches x) :
    2 ^ k ≤ cert.length := by
  have h := pow_le_length_of_covers (L := cert.map Pattern.ys) fun x hx => by
    obtain ⟨p, hp, hm⟩ := hcover x hx
    have heval := hvalid p hp x hm
    subst hx
    exact List.mem_map.mpr ⟨p, hp, (copyCNF_eval_eq (hys p hp) heval).symm⟩
  simpa using h

/-! ## Collapsing `∃` positions does not help

A pattern may also leave an `∃` variable as `*`, meaning every value of it works. Such a
pattern passes only if the pattern with that variable fixed to `false` also passes, and both
cover the same `x̄`. So `∃`-wildcards never reduce the number of patterns. -/

/-- A pattern where both `∀` and `∃` positions may be `*` (`none`). -/
structure WildPattern where
  xs : List (Option Bool)
  ys : List (Option Bool)

/-- Fix every `∃`-wildcard to `false`. -/
def WildPattern.fill (p : WildPattern) : Pattern := ⟨p.xs, p.ys.map (·.getD false)⟩

/-- `x` is covered by the pattern's `∀` positions. -/
def WildPattern.Matches (p : WildPattern) (x : Assignment) : Prop := p.fill.Matches x

/-- The pattern passes its TAUTOLOGY query: `φ` holds on every covered `x` and every `y`
fitting the `∃` positions. -/
def WildPattern.Valid (φ : CNF) (p : WildPattern) : Prop :=
  ∀ x : Assignment, p.Matches x → ∀ y : Assignment, (Pattern.mk p.ys []).Matches y →
    φ.eval (x ++ y) = true

theorem WildPattern.valid_fill {φ : CNF} {p : WildPattern} (h : p.Valid φ) : p.fill.Valid φ := by
  intro x hx
  apply h x hx
  refine ⟨by simp [WildPattern.fill], fun i b hb => ?_⟩
  simp [WildPattern.fill, List.getElem?_map, hb]

/-- `∃`-wildcards do not help: a certificate of wild patterns for the copy instance still
needs at least `2^k` patterns. -/
theorem wildPattern_certificate_lower_bound (k : Nat) (cert : List WildPattern)
    (hys : ∀ p ∈ cert, p.ys.length = k)
    (hvalid : ∀ p ∈ cert, p.Valid (copyCNF k))
    (hcover : ∀ x : Assignment, x.length = k → ∃ p ∈ cert, p.Matches x) :
    2 ^ k ≤ cert.length := by
  have h := pattern_certificate_lower_bound k (cert.map WildPattern.fill)
    (by simp only [List.mem_map]; rintro _ ⟨p, hp, rfl⟩; simp [WildPattern.fill, hys p hp])
    (by simp only [List.mem_map]; rintro _ ⟨p, hp, rfl⟩; exact WildPattern.valid_fill (hvalid p hp))
    (fun x hx => by
      obtain ⟨p, hp, hm⟩ := hcover x hx
      exact ⟨p.fill, List.mem_map.mpr ⟨p, hp, rfl⟩, hm⟩)
  simpa using h

end Pspace2ndlevelsmash
