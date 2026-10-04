import Pspace2ndlevelsmash.Quantifiers

/-!
# Runnable evaluation

`evalB` is a brute-force `Bool` evaluator for TQBF, proved to agree with `Eval`. It is the
reference answer for testing. `tautB` is a brute-force TAUTOLOGY check, proved to agree with
`Tautology`; it plays the oracle in tests.
-/

namespace Pspace2ndlevelsmash

/-- Brute-force evaluation: try both values of every quantified variable. -/
def evalB : Prefix → CNF → Assignment → Bool
  | [], φ, pre => φ.eval pre
  | .all :: qs, φ, pre => evalB qs φ (pre ++ [false]) && evalB qs φ (pre ++ [true])
  | .ex :: qs, φ, pre => evalB qs φ (pre ++ [false]) || evalB qs φ (pre ++ [true])

theorem evalB_iff (qs : Prefix) (φ : CNF) (pre : Assignment) :
    evalB qs φ pre = true ↔ Eval qs φ pre := by
  induction qs generalizing pre with
  | nil => rfl
  | cons q qs ih =>
    cases q <;> simp [evalB, Bool.forall_bool, Bool.exists_bool, ih]

instance (qs : Prefix) (φ : CNF) (pre : Assignment) : Decidable (Eval qs φ pre) :=
  decidable_of_iff _ (evalB_iff qs φ pre)

/-- Brute-force TAUTOLOGY: evaluate `ψ` under `n` universal quantifiers. -/
def tautB (ψ : CNF) (n : Nat) : Bool := evalB (List.replicate n .all) ψ []

theorem tautB_iff (ψ : CNF) (n : Nat) : tautB ψ n = true ↔ Tautology ψ n := by
  have hall : AllForall (List.replicate n .all) := fun q hq => (List.mem_replicate.mp hq).2
  rw [tautB, evalB_iff, eval_iff_tautology_of_allForall hall, tautology_restrict_iff]
  simp [Tautology]

end Pspace2ndlevelsmash
