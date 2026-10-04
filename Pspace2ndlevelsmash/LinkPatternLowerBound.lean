import Pspace2ndlevelsmash.PatternLowerBound

/-!
# Link patterns need exponentially many queries

A *link pattern* extends a pattern: each `∃` position may be a constant, `?ⱼ` ("same as `∀`
variable `j`") or `!ⱼ` ("opposite of `∀` variable `j`"). Checking one link pattern is still
one TAUTOLOGY query. Link patterns verify the copy formula with a single pattern.

For the XOR formula `(y₁ ↔ a₁ ⊕ b₁) ∧ … ∧ (yₖ ↔ aₖ ⊕ bₖ)`, which has `4k` clauses and is
true, every link-pattern certificate has at least `2^k` patterns: a valid pattern must fix
`aᵢ` or `bᵢ` for every `i`, because `aᵢ ⊕ bᵢ` is not a constant or a single linked variable.
-/

namespace Pspace2ndlevelsmash

/-! ## The XOR formula -/

/-- `(y₀ ↔ a₀ ⊕ b₀) ∧ … ∧ (yₖ₋₁ ↔ aₖ₋₁ ⊕ bₖ₋₁)` with `aᵢ` as variable `2i`, `bᵢ` as `2i + 1`
and `yᵢ` as `2k + i`. -/
def xorCNF (k : Nat) : CNF :=
  (List.range k).flatMap fun i =>
    [[⟨2 * k + i, false⟩, ⟨2 * i, true⟩, ⟨2 * i + 1, true⟩],
     [⟨2 * k + i, false⟩, ⟨2 * i, false⟩, ⟨2 * i + 1, false⟩],
     [⟨2 * k + i, true⟩, ⟨2 * i, false⟩, ⟨2 * i + 1, true⟩],
     [⟨2 * k + i, true⟩, ⟨2 * i, true⟩, ⟨2 * i + 1, false⟩]]

theorem getD_append_of_lt {l l' : Assignment} {n : Nat} (h : n < l.length) :
    (l ++ l').getD n false = l.getD n false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_of_ge {l l' : Assignment} {n : Nat} (h : l.length ≤ n) :
    (l ++ l').getD n false = l'.getD (n - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- The XOR formula holds only when each `yᵢ` is `aᵢ ⊕ bᵢ`. -/
theorem xorCNF_eval_spec {k : Nat} {x y : Assignment} (hx : x.length = 2 * k)
    (h : (xorCNF k).eval (x ++ y) = true) {i : Nat} (hi : i < k) :
    y.getD i false = (x.getD (2 * i) false ^^ x.getD (2 * i + 1) false) := by
  simp only [CNF.eval, List.all_eq_true] at h
  have mem : ∀ c, c = [⟨2 * k + i, false⟩, ⟨2 * i, true⟩, ⟨2 * i + 1, true⟩] ∨
      c = [⟨2 * k + i, false⟩, ⟨2 * i, false⟩, ⟨2 * i + 1, false⟩] ∨
      c = [⟨2 * k + i, true⟩, ⟨2 * i, false⟩, ⟨2 * i + 1, true⟩] ∨
      c = [⟨2 * k + i, true⟩, ⟨2 * i, true⟩, ⟨2 * i + 1, false⟩] → c ∈ xorCNF k := by
    intro c hc
    simp only [xorCNF, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
      or_false]
    exact ⟨i, hi, hc⟩
  have h₁ := h _ (mem _ (.inl rfl))
  have h₂ := h _ (mem _ (.inr (.inl rfl)))
  have h₃ := h _ (mem _ (.inr (.inr (.inl rfl))))
  have h₄ := h _ (mem _ (.inr (.inr (.inr rfl))))
  simp only [Clause.eval, Literal.eval, List.any_cons, List.any_nil, Bool.or_false,
    getD_append_of_lt (show 2 * i < x.length by omega),
    getD_append_of_lt (show 2 * i + 1 < x.length by omega),
    getD_append_of_ge (show x.length ≤ 2 * k + i by omega),
    show 2 * k + i - x.length = i by omega] at h₁ h₂ h₃ h₄
  revert h₁ h₂ h₃ h₄
  cases x.getD (2 * i) false <;> cases x.getD (2 * i + 1) false <;> cases y.getD i false <;>
    decide

/-- The XOR formula holds when each `yᵢ` is `aᵢ ⊕ bᵢ`. -/
theorem xorCNF_eval_self {k : Nat} {x : Assignment} (hx : x.length = 2 * k) :
    (xorCNF k).eval
      (x ++ (List.range k).map fun i => x.getD (2 * i) false ^^ x.getD (2 * i + 1) false) =
        true := by
  simp only [CNF.eval, List.all_eq_true]
  intro c hc
  simp only [xorCNF, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at hc
  obtain ⟨i, hi, hc⟩ := hc
  have hy : ((List.range k).map fun i => x.getD (2 * i) false ^^ x.getD (2 * i + 1) false).getD
      i false = (x.getD (2 * i) false ^^ x.getD (2 * i + 1) false) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [Clause.eval, Literal.eval, List.any_cons, List.any_nil, Bool.or_false,
      getD_append_of_lt (show 2 * i < x.length by omega),
      getD_append_of_lt (show 2 * i + 1 < x.length by omega),
      getD_append_of_ge (show x.length ≤ 2 * k + i by omega),
      show 2 * k + i - x.length = i by omega, hy] <;>
    cases x.getD (2 * i) false <;> cases x.getD (2 * i + 1) false <;> decide

/-- The XOR instance `∀ā ∀b̄ ∃ȳ, ∧ᵢ yᵢ = aᵢ ⊕ bᵢ` is true. -/
theorem xor_holds (k : Nat) :
    Eval (List.replicate (2 * k) .all ++ List.replicate k .ex) (xorCNF k) [] := by
  have h := eval_all_ex_all_iff (alls₁ := List.replicate (2 * k) .all)
    (exs := List.replicate k .ex) (alls₂ := [])
    (fun q hq => (List.mem_replicate.mp hq).2) (fun q hq => (List.mem_replicate.mp hq).2)
    (fun _ h => nomatch h) (xorCNF k) []
  rw [List.append_nil] at h
  rw [h]
  intro x hx
  simp only [List.length_replicate] at hx
  refine ⟨(List.range k).map fun i => x.getD (2 * i) false ^^ x.getD (2 * i + 1) false,
    by simp, ?_⟩
  rw [tautology_restrict_iff]
  intro a ha
  cases a with
  | nil => simpa using xorCNF_eval_self hx
  | cons _ _ => cases ha

/-! ## Link patterns -/

/-- The value of an `∃` position in a link pattern. -/
inductive YVal where
  /-- A fixed value. -/
  | const (b : Bool)
  /-- `?ⱼ`: same as `∀` variable `j`. -/
  | link (j : Nat)
  /-- `!ⱼ`: opposite of `∀` variable `j`. -/
  | anti (j : Nat)

def YVal.eval (x : Assignment) : YVal → Bool
  | .const b => b
  | .link j => x.getD j false
  | .anti j => !x.getD j false

/-- A link pattern: each `∀` variable fixed or `*` (`none`), and each `∃` variable a `YVal`. -/
structure LinkPattern where
  xs : List (Option Bool)
  ys : List YVal

/-- `x` is one of the `∀` assignments covered by the pattern. -/
def LinkPattern.Covers (p : LinkPattern) (x : Assignment) : Prop :=
  x.length = p.xs.length ∧ ∀ (j : Nat) (b : Bool), p.xs[j]? = some (some b) → x[j]? = some b

/-- The pattern passes its TAUTOLOGY query: `φ` holds on every covered `x`, with the `∃`
variables set by the pattern. -/
def LinkPattern.Valid (φ : CNF) (p : LinkPattern) : Prop :=
  ∀ x : Assignment, p.Covers x → φ.eval (x ++ p.ys.map (YVal.eval x)) = true

/-! ## A valid pattern fixes `aᵢ` or `bᵢ` -/

/-- The pattern's fixed values, with `*` read as `false`. -/
def LinkPattern.fill (p : LinkPattern) : Assignment := p.xs.map (·.getD false)

/-- `p.fill` with `aᵢ := u` and `bᵢ := v`. -/
def LinkPattern.variant (p : LinkPattern) (i : Nat) (u v : Bool) : Assignment :=
  (p.fill.set (2 * i) u).set (2 * i + 1) v

theorem LinkPattern.covers_variant {p : LinkPattern} {i : Nat}
    (ha : p.xs[2 * i]? = some none) (hb : p.xs[2 * i + 1]? = some none) (u v : Bool) :
    p.Covers (p.variant i u v) := by
  refine ⟨by simp [variant, fill], fun j b hj => ?_⟩
  have hja : 2 * i ≠ j := by rintro rfl; simp [ha] at hj
  have hjb : 2 * i + 1 ≠ j := by rintro rfl; simp [hb] at hj
  simp [variant, fill, List.getElem?_set_ne hja, List.getElem?_set_ne hjb, hj]

theorem LinkPattern.getD_variant_a {p : LinkPattern} {i : Nat} (h : 2 * i + 1 < p.xs.length)
    (u v : Bool) : (p.variant i u v).getD (2 * i) false = u := by
  simp [variant, fill, List.getD_eq_getElem?_getD, show 2 * i < p.xs.length by omega]

theorem LinkPattern.getD_variant_b {p : LinkPattern} {i : Nat} (h : 2 * i + 1 < p.xs.length)
    (u v : Bool) : (p.variant i u v).getD (2 * i + 1) false = v := by
  simp [variant, fill, List.getD_eq_getElem?_getD, h]

theorem LinkPattern.getD_variant_ne {p : LinkPattern} {i j : Nat} (ha : j ≠ 2 * i)
    (hb : j ≠ 2 * i + 1) (u v : Bool) :
    (p.variant i u v).getD j false = p.fill.getD j false := by
  simp [variant, List.getD_eq_getElem?_getD, Ne.symm ha, Ne.symm hb]

/-- A valid link pattern for the XOR formula cannot leave both `aᵢ` and `bᵢ` as `*`. -/
theorem LinkPattern.fixes_one {k : Nat} {p : LinkPattern} (hlen : p.xs.length = 2 * k)
    (hv : p.Valid (xorCNF k)) {i : Nat} (hi : i < k)
    (ha : p.xs[2 * i]? = some none) (hb : p.xs[2 * i + 1]? = some none) : False := by
  have hlt : 2 * i + 1 < p.xs.length := by omega
  have hy : ∀ u v, (p.ys.getD i (.const false)).eval (p.variant i u v) = (u ^^ v) := by
    intro u v
    have hc := p.covers_variant ha hb u v
    have := xorCNF_eval_spec (by rw [hc.1, hlen]) (hv _ hc) hi
    rw [getD_variant_a hlt, getD_variant_b hlt] at this
    rw [← this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases p.ys[i]? <;> rfl
  have h₀ := hy false false
  have h₁ := hy false true
  have h₂ := hy true false
  cases hyi : p.ys.getD i (.const false) with
  | const c =>
    simp only [hyi, YVal.eval] at h₀ h₁
    simp_all
  | link j =>
    simp only [hyi, YVal.eval] at h₀ h₁ h₂
    by_cases hja : j = 2 * i
    · subst hja; rw [getD_variant_a hlt] at h₁; simp at h₁
    · by_cases hjb : j = 2 * i + 1
      · subst hjb; rw [getD_variant_b hlt] at h₂; simp at h₂
      · simp only [getD_variant_ne hja hjb] at h₀ h₁; simp_all
  | anti j =>
    simp only [hyi, YVal.eval] at h₀ h₁ h₂
    by_cases hja : j = 2 * i
    · subst hja; rw [getD_variant_a hlt] at h₀; simp at h₀
    · by_cases hjb : j = 2 * i + 1
      · subst hjb; rw [getD_variant_b hlt] at h₀; simp at h₀
      · simp only [getD_variant_ne hja hjb] at h₀ h₁; simp_all

/-! ## Counting -/

theorem length_flatMap_const {α β : Type} {l : List α} {f : α → List β} {c : Nat}
    (h : ∀ a ∈ l, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (List.mem_cons_self ..),
      ih fun a ha => h a (List.mem_cons_of_mem _ ha), List.length_cons, Nat.succ_mul]
    omega

/-- All assignments of length `n`. -/
def allBits : Nat → List Assignment
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap fun r => [false :: r, true :: r]

theorem length_allBits (n : Nat) : (allBits n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allBits, length_flatMap_const (c := 2) (fun _ _ => rfl), ih, Nat.pow_succ]

theorem mem_allBits {n : Nat} {r : Assignment} (h : r.length = n) : r ∈ allBits n := by
  induction n generalizing r with
  | zero => cases r with
    | nil => simp [allBits]
    | cons _ _ => cases h
  | succ n ih => cases r with
    | nil => cases h
    | cons b r =>
      simp only [allBits, List.mem_flatMap]
      exact ⟨r, ih (by simpa using h), by cases b <;> simp⟩

/-- Rebuild a covered assignment from the pattern and one free bit per pair. -/
def LinkPattern.decode (p : LinkPattern) (r : Assignment) : Assignment :=
  (List.range p.xs.length).map fun j =>
    match p.xs[j]? with
    | some (some b) => b
    | _ => r.getD (j / 2) false

/-- The free bit of each pair: `aᵢ` if it is `*`, otherwise `bᵢ`. -/
def LinkPattern.pick (k : Nat) (p : LinkPattern) (x : Assignment) : Assignment :=
  (List.range k).map fun i =>
    if p.xs[2 * i]? = some none then x.getD (2 * i) false else x.getD (2 * i + 1) false

/-- A covered assignment is determined by the pattern and `k` bits. -/
theorem LinkPattern.decode_pick {k : Nat} {p : LinkPattern} (hlen : p.xs.length = 2 * k)
    (hv : p.Valid (xorCNF k)) {x : Assignment} (hx : p.Covers x) :
    p.decode (p.pick k x) = x := by
  apply List.ext_getElem (by simp [decode, hx.1])
  intro j hj₁ hj₂
  have hj : j < 2 * k := by simp [decode] at hj₁; omega
  simp only [decode, List.getElem_map, List.getElem_range]
  have hpj : p.xs[j]? = some p.xs[j] := List.getElem?_eq_getElem (by omega)
  cases hxj : p.xs[j] with
  | some b =>
    rw [hpj, hxj]
    have := hx.2 j b (by rw [hpj, hxj])
    rw [List.getElem?_eq_getElem hj₂] at this
    exact (Option.some.inj this).symm
  | none =>
    rw [hpj, hxj]
    simp only [pick, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show j / 2 < k by omega), Option.map_some, Option.getD_some]
    rcases (show j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 by omega) with hje | hjo
    · rw [ite_eq_left (by rw [← hje, hpj, hxj]), ← hje, List.getElem?_eq_getElem hj₂]; rfl
    · rw [ite_eq_right (fun ha => p.fixes_one hlen hv (show j / 2 < k by omega) ha
        (by rw [← hjo, hpj, hxj])), ← hjo, List.getElem?_eq_getElem hj₂]; rfl

/-- Any link-pattern certificate for the XOR instance with `k` pairs has at least `2^k`
patterns, so the verifier makes at least `2^k` TAUTOLOGY queries. -/
theorem linkPattern_certificate_lower_bound (k : Nat) (cert : List LinkPattern)
    (hxs : ∀ p ∈ cert, p.xs.length = 2 * k)
    (hvalid : ∀ p ∈ cert, p.Valid (xorCNF k))
    (hcover : ∀ x : Assignment, x.length = 2 * k → ∃ p ∈ cert, p.Covers x) :
    2 ^ k ≤ cert.length := by
  have h := pow_le_length_of_covers (k := 2 * k)
    (L := cert.flatMap fun p => (allBits k).map p.decode) fun x hx => by
      obtain ⟨p, hp, hc⟩ := hcover x hx
      refine List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨p.pick k x, ?_, ?_⟩⟩
      · exact mem_allBits (by simp [LinkPattern.pick])
      · exact LinkPattern.decode_pick (hxs p hp) (hvalid p hp) hc
  rw [length_flatMap_const (c := 2 ^ k) (fun p _ => by simp [length_allBits]),
    Nat.two_mul, Nat.pow_add] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos k)

end Pspace2ndlevelsmash
