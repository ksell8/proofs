import Pspace2ndlevelsmash

open Pspace2ndlevelsmash

/-- Test a procedure on random 3-CNF instances with `n` variables and `4n` clauses. -/
def runTests (name : String) (proc : Procedure) : IO Unit := do
  IO.println s!"{name}"
  IO.println "  n   wrong   max queries   avg queries"
  for n in [2:13] do
    let r ← testProcedure proc n (4 * n) 3 200
    let avg := r.totalQueries.toFloat / r.instances.toFloat
    IO.println s!"  {n}   {r.wrong.length}   {r.maxQueries}   {avg}"
    for (qs, φ) in r.wrong.take 1 do
      IO.println s!"    counterexample: {repr qs} {repr φ}"

def main : IO Unit :=
  runTests "baseline" baseline
