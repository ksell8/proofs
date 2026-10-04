import Pspace2ndlevelsmash.Decide

/-!
# Test harness

A `Procedure` decides a TQBF instance using a TAUTOLOGY oracle. The harness hands it a
counting oracle, checks its answer against `evalB` on random instances, and reports how
many oracle queries it made.

The oracle takes a concrete formula `ψ` and a variable count `n` and answers whether `ψ` is
a tautology over `n` variables. A procedure should only learn about `φ` through the oracle;
the harness does not enforce this, so it is up to the procedure's author.
-/

namespace Pspace2ndlevelsmash

/-- A TAUTOLOGY oracle that counts its queries in the state. -/
abbrev Oracle := CNF → Nat → StateM Nat Bool

def countingOracle : Oracle := fun ψ n => do
  modify (· + 1)
  return tautB ψ n

/-- A decision procedure for TQBF that may query a TAUTOLOGY oracle. -/
abbrev Procedure := Oracle → Prefix → CNF → StateM Nat Bool

/-- Naive baseline: branch on quantifiers until the remaining prefix is all `∀`, then ask
the oracle once about the restricted formula. Uses about 2^(number of variables before the
last `∀` block) queries. -/
def baselineAux (taut : Oracle) (φ : CNF) : Prefix → Assignment → StateM Nat Bool
  | [], pre => taut (φ.restrict pre) 0
  | .all :: qs, pre =>
    if qs.all (· == .all) then taut (φ.restrict pre) (qs.length + 1)
    else do
      if !(← baselineAux taut φ qs (pre ++ [false])) then return false
      baselineAux taut φ qs (pre ++ [true])
  | .ex :: qs, pre => do
    if ← baselineAux taut φ qs (pre ++ [false]) then return true
    baselineAux taut φ qs (pre ++ [true])

def baseline : Procedure := fun taut qs φ => baselineAux taut φ qs []

/-! ## Random instances -/

def randomPrefix (n : Nat) : IO Prefix :=
  (List.range n).mapM fun _ => do return if (← IO.rand 0 1) == 0 then .all else .ex

/-- A random CNF with `m` clauses of width `k` over variables `0, …, n - 1`. -/
def randomCNF (n m k : Nat) : IO CNF :=
  (List.range m).mapM fun _ => (List.range k).mapM fun _ => do
    return { var := ← IO.rand 0 (n - 1), pos := (← IO.rand 0 1) == 1 }

/-! ## Running tests -/

structure Report where
  instances : Nat := 0
  wrong : List (Prefix × CNF) := []
  maxQueries : Nat := 0
  totalQueries : Nat := 0

/-- Run `proc` on `count` random instances with `n` variables, `m` clauses of width `k`. -/
def testProcedure (proc : Procedure) (n m k count : Nat) : IO Report := do
  let mut r : Report := {}
  for _ in [0:count] do
    let qs ← randomPrefix n
    let φ ← randomCNF n m k
    let (answer, queries) := (proc countingOracle qs φ).run 0
    r := { r with
      instances := r.instances + 1
      wrong := if answer == evalB qs φ [] then r.wrong else (qs, φ) :: r.wrong
      maxQueries := max r.maxQueries queries
      totalQueries := r.totalQueries + queries }
  return r

end Pspace2ndlevelsmash
