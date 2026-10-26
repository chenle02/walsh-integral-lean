/-
SPDX-License-Identifier: Apache-2.0
Environment-loading interface from leanprover-community/axiom-audit
46024e005996495c65ef609368e11ab39c4222e3, as used by the Gromov benchmark.
The collector is the benchmark's shared-cache AxiomAudit.axiomsOf. Its
project-wide allowlist result is sound for axiom-clean imports; per-declaration
lists can undercount within cyclic clusters. Exact types use kernel Expr repr.
-/
module

import AxiomAudit

public section

open Lean AxiomAudit

private def copied (s : String) : String := s.foldl (fun acc c => acc.push c) ""

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: axiom-audit Module ..."
    return 2
  let modules := args.toArray.map String.toName
  let (output, ok) ← withImportedEnv modules <|
    withReader (fun (ctx : Core.Context) => {ctx with maxHeartbeats := 0}) <|
    withOptions (fun o => (o.setBool `pp.universes true).setBool `pp.numericTypes true) do
    let env ← getEnv
    let moduleNames := env.allImportedModuleNames
    let candidates := (env.constants.fold (init := #[]) fun acc name _ =>
      match env.getModuleIdxFor? name with
      | some idx => if modules.contains moduleNames[idx.toNat]! then acc.push name else acc
      | none => acc).qsort Name.lt
    let perDecl : Array (Array Name) := (candidates.mapM axiomsOf |>.run env).run' {}
    let mut rows : Array Json := #[]
    let mut ok := !candidates.isEmpty
    for i in [0:candidates.size] do
      let name := candidates[i]!
      let some info := env.find? name | throwError "Missing declaration {name}"
      let some idx := env.getModuleIdxFor? name | throwError "Missing owner {name}"
      let axioms := perDecl[i]!
      let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
      if axioms.any (!allowed.contains ·) then ok := false
      let type := reprStr info.type
      rows := rows.push (Json.mkObj [
        ("name", Json.str (freshStr name)),
        ("module", Json.str (freshStr moduleNames[idx.toNat]!)),
        ("type_expr", Json.str (copied type)),
        ("axioms", toJson (axioms.map freshStr))])
    pure (Json.mkObj [
      ("schema", Json.str "lean-library-native-owned-audit/1"),
      ("modules", toJson (modules.map freshStr)),
      ("owned_count", toJson rows.size),
      ("ok", Json.bool ok),
      ("declarations", Json.arr rows)], ok)
  IO.println output.compress
  return if ok then 0 else 1
