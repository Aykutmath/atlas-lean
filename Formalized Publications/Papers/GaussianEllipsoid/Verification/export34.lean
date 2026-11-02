/-
Faithful NDJSON exporter for Lean 4.34 environments, replicating the
official 4.35 `LeanExport.Basic` format (format version 3.1.0) so that
original-pin (4.34) elaborations can be judged by the official 4.35
`lake comparator` from untrusted export data alone.

Scope and honesty notes:
- This tool only SERIALIZES an already-elaborated 4.34 `Environment`
  (loaded from prebuilt oleans via `withImportModules`; no source is
  re-elaborated here, and no 4.34 olean is ever loaded into a 4.35
  process). The emitted NDJSON carries honest metadata (this
  exporter's name plus the real 4.34 `versionString`/`githash`); only
  the `format` version claims compatibility, namely "3.1.0".
- The tool's own entry point is `unsafe` only because environment
  loading (`withImportModules`) is an unsafe IO operation. That
  unsafety lives entirely in this external export utility, is never
  part of the challenge or the solution, and buys nothing: the NDJSON
  it emits is untrusted data, re-parsed from scratch and kernel-checked
  by the official judge, which independently rejects `unsafe` and
  nonstandard axioms in the solution.
- Every `ConstantInfo` variant is emitted with all of its fields
  (types, values, bodies, safety flags, reducibility hints, universe
  params, inductive/ctor/recursor structure, recursor rules); `unsafe`
  constants are SKIPPED exactly like the official default (never
  silently trusted), and anything the format cannot represent
  (free/meta variables, level mvars, missing constants, surviving
  `mdata`) is a hard refusal, never a silent downgrade.
- `mdata` is stripped by default, exactly like the official default
  (`exportMData` off).

Usage:
  lean --run export34.lean <Module> -- <root1> <root2> ... > out.ndjson
with LEAN_PATH pointing at the prebuilt oleans for <Module>.
-/
import Lean

open Lean Std

namespace Export34

structure State where
  names : HashMap Name Nat := HashMap.emptyWithCapacity 200000 |>.insert .anonymous 0
  levels : HashMap Level Nat := HashMap.emptyWithCapacity 1000 |>.insert .zero 0
  exprs : HashMap Expr Nat := HashMap.emptyWithCapacity 100000
  consts : HashSet Name := HashSet.emptyWithCapacity 200000
  recMap : List (Name × List Name) := []
  current : Name := .anonymous

abbrev M := ReaderT Environment $ StateT State IO

def refuse (msg : String) : M α := do
  let st ← get
  throw (.userError s!"export34 REFUSED (while exporting {st.current} consts={st.consts.size} names={st.names.size} exprs={st.exprs.size}): {msg}")

def findRecs (ind : Name) : M (List Name) := do
  match (← get).recMap.find? (fun p => p.1 == ind) with
  | some (_, rs) => return rs
  | none => return []

mutual

partial def dumpName (n : Name) : M Nat := do
  if let some idx := (← get).names[n]? then
    return idx
  let payload : Json ← match n with
    | .anonymous => refuse "anonymous name"
    | .str p s =>
      let pre ← dumpName p
      pure (Json.mkObj [("str", .mkObj [("pre", pre), ("str", s)])])
    | .num p i =>
      let pre ← dumpName p
      pure (Json.mkObj [("num", .mkObj [("pre", pre), ("i", i)])])
  let idx := (← get).names.size
  IO.println ((payload.setObjVal! "in" idx).compress)
  modify fun st => { st with names := st.names.insert n idx }
  return idx

partial def dumpLevel (l : Level) : M Nat := do
  if let some idx := (← get).levels[l]? then
    return idx
  let payload : Json ← match l with
    | .zero => refuse "level zero revisited unbound"
    | .mvar _ => refuse "level metavariable"
    | .succ l =>
      let i ← dumpLevel l
      pure (Json.mkObj [("succ", i)])
    | .max l1 l2 =>
      let i1 ← dumpLevel l1
      let i2 ← dumpLevel l2
      pure (Json.mkObj [("max", Json.arr #[i1, i2])])
    | .imax l1 l2 =>
      let i1 ← dumpLevel l1
      let i2 ← dumpLevel l2
      pure (Json.mkObj [("imax", Json.arr #[i1, i2])])
    | .param n =>
      let i ← dumpName n
      pure (Json.mkObj [("param", i)])
  let idx := (← get).levels.size
  IO.println ((payload.setObjVal! "il" idx).compress)
  modify fun st => { st with levels := st.levels.insert l idx }
  return idx

end

def dumpUparams (up : List Name) : M Json := do
  let idxs ← up.mapM dumpName
  for u in up do
    let _ ← dumpLevel (.param u)
  pure idxs.toJson

def dumpNames (ns : List Name) : M Json := do
  pure (← ns.mapM dumpName).toJson

/-- Strip `mdata` (official default: `exportMData` off). -/
partial def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n d b bi => .lam n (stripMData d) (stripMData b) bi
  | .forallE n d b bi => .forallE n (stripMData d) (stripMData b) bi
  | .letE n d v b _ => .letE n (stripMData d) (stripMData v) (stripMData b) false
  | .proj s i e => .proj s i (stripMData e)
  | e => e

def binderToJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def hintsToJson : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular n => .mkObj [("regular", n.toNat)]

def safetyToJson : DefinitionSafety → Json
  | .«unsafe» => "unsafe"
  | .safe => "safe"
  | .«partial» => "partial"

def quotKindToJson : QuotKind → Json
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

mutual

partial def dumpExprAux (e : Expr) : M Nat := do
  if let some idx := (← get).exprs[e]? then
    return idx
  let payload : Json ← match e with
    | .fvar .. => refuse "free variable in exported term"
    | .mvar .. => refuse "metavariable in exported term"
    | .mdata .. => refuse "mdata survived stripping"
    | .bvar i => pure (Json.mkObj [("bvar", i)])
    | .lit (.natVal i) => do
      dumpNatDeps
      pure (Json.mkObj [("natVal", s!"{i}")])
    | .lit (.strVal s) => do
      dumpStrDeps
      pure (Json.mkObj [("strVal", s)])
    | .sort l =>
      let i ← dumpLevel l
      pure (Json.mkObj [("sort", i)])
    | .const n us =>
      let ni ← dumpName n
      let uis ← us.mapM dumpLevel
      pure (Json.mkObj [("const", .mkObj [("name", ni), ("us", uis.toJson)])])
    | .app f a =>
      let fi ← dumpExprAux f
      let ai ← dumpExprAux a
      pure (Json.mkObj [("app", .mkObj [("fn", fi), ("arg", ai)])])
    | .lam n d b bi =>
      let ni ← dumpName n
      let di ← dumpExprAux d
      let bi2 ← dumpExprAux b
      pure (Json.mkObj [("lam", .mkObj [("name", ni), ("type", di),
        ("body", bi2), ("binderInfo", binderToJson bi)])])
    | .forallE n d b bi =>
      let ni ← dumpName n
      let di ← dumpExprAux d
      let bi2 ← dumpExprAux b
      pure (Json.mkObj [("forallE", .mkObj [("name", ni), ("type", di),
        ("body", bi2), ("binderInfo", binderToJson bi)])])
    | .letE n d v b nondep =>
      let ni ← dumpName n
      let di ← dumpExprAux d
      let vi ← dumpExprAux v
      let bi2 ← dumpExprAux b
      pure (Json.mkObj [("letE", .mkObj [("name", ni), ("type", di),
        ("value", vi), ("body", bi2), ("nondep", nondep)])])
    | .proj s i e =>
      let si ← dumpName s
      let ei ← dumpExprAux e
      pure (Json.mkObj [("proj", .mkObj [("typeName", si), ("idx", i),
        ("struct", ei)])])
  let idx := (← get).exprs.size
  IO.println ((payload.setObjVal! "ie" idx).compress)
  modify fun st => { st with exprs := st.exprs.insert e idx }
  return idx

partial def dumpExpr (e : Expr) : M Nat :=
  dumpExprAux (stripMData e)

partial def dumpDeps (e : Expr) : M Unit := do
  for c in e.getUsedConstants do
    dumpConstant c

partial def dumpNatDeps : M Unit := do
  let env ← read
  let nat : Name := ``Nat
  if !(← get).consts.contains nat && (env.find? nat).isSome then
    dumpConstant nat

partial def dumpStrDeps : M Unit := do
  let env ← read
  let charOfNat : Name := ``Char.ofNat
  if !(← get).consts.contains charOfNat && (env.find? charOfNat).isSome then
    dumpConstant charOfNat
  let stringOfList : Name := ``String.ofList
  if !(← get).consts.contains stringOfList && (env.find? stringOfList).isSome then
    dumpConstant stringOfList

partial def dumpRecRule (rule : RecursorRule) : M Json := do
  let ci ← dumpName rule.ctor
  let ri ← dumpExpr rule.rhs
  pure (Json.mkObj [("ctor", ci), ("nfields", rule.nfields), ("rhs", ri)])

partial def dumpConstant (c : Name) : M Unit := do
  let env ← read
  let some ci := env.find? c
    | refuse s!"constant not found in environment: {c}"
  -- Official default (`exportUnsafe` off): skip unsafe constants rather
  -- than trusting them. Skipping is fail-closed: the comparator reports
  -- any reachable-but-absent constant instead of passing.
  if ci.isUnsafe then
    return
  if (← get).consts.contains c then
    return
  modify fun st => { st with consts := st.consts.insert c }
  match ci with
  | .axiomInfo val => do
    dumpDeps val.type
    let ni ← dumpName val.name
    let lp ← dumpUparams val.levelParams
    let ti ← dumpExpr val.type
    IO.println ((Json.mkObj [("axiom", .mkObj [("name", ni),
      ("levelParams", lp), ("type", ti), ("isUnsafe", val.isUnsafe)])]).compress)
  | .defnInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    let ni ← dumpName val.name
    let lp ← dumpUparams val.levelParams
    let ti ← dumpExpr val.type
    let vi ← dumpExpr val.value
    let al ← dumpNames val.all
    IO.println ((Json.mkObj [("def", .mkObj [("name", ni),
      ("levelParams", lp), ("type", ti), ("value", vi),
      ("hints", hintsToJson val.hints), ("safety", safetyToJson val.safety),
      ("all", al)])]).compress)
  | .opaqueInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    let ni ← dumpName val.name
    let lp ← dumpUparams val.levelParams
    let ti ← dumpExpr val.type
    let vi ← dumpExpr val.value
    let al ← dumpNames val.all
    IO.println ((Json.mkObj [("opaque", .mkObj [("name", ni),
      ("levelParams", lp), ("type", ti), ("value", vi),
      ("all", al), ("isUnsafe", val.isUnsafe)])]).compress)
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    let ni ← dumpName val.name
    let lp ← dumpUparams val.levelParams
    let ti ← dumpExpr val.type
    let vi ← dumpExpr val.value
    let al ← dumpNames val.all
    IO.println ((Json.mkObj [("thm", .mkObj [("name", ni),
      ("levelParams", lp), ("type", ti), ("value", vi),
      ("all", al)])]).compress)
  | .quotInfo _ => do
    dumpConstant ``Eq
    for q in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let some (.quotInfo val) := env.find? q
        | refuse s!"Quot constant not found: {q}"
      if val.name != q then
        refuse s!"Quot package mismatch at {q}"
      modify fun st => { st with consts := st.consts.insert q }
      let ni ← dumpName val.name
      let lp ← dumpUparams val.levelParams
      let ti ← dumpExpr val.type
      IO.println ((Json.mkObj [("quot", .mkObj [("name", ni),
        ("levelParams", lp), ("type", ti),
        ("kind", quotKindToJson val.kind)])]).compress)
  | .inductInfo baseVal => do
    -- Collect the mutual block: inductives, ctors, recursors.
    let mut indVals : Array InductiveVal := #[]
    let mut ctorVals : Array ConstructorVal := #[]
    let mut recNames : List Name := []
    for indName in baseVal.all do
      let some indCi := env.find? indName
        | refuse s!"inductive block member not found: {indName}"
      let .inductInfo val := indCi
        | refuse s!"expected inductive block member: {indName}"
      if val.isUnsafe then
        refuse s!"unsafe inductive in trusted export: {indName}"
      indVals := indVals.push val
      for ctor in val.ctors do
        let some ctorCi := env.find? ctor
          | refuse s!"constructor not found: {ctor}"
        let .ctorInfo ctorVal := ctorCi
          | refuse s!"expected constructor: {ctor}"
        if ctorVal.isUnsafe then
          refuse s!"unsafe constructor in trusted export: {ctor}"
        ctorVals := ctorVals.push ctorVal
      modify fun st => { st with consts := st.consts.insert indName }
      dumpDeps val.type
      for r in (← findRecs baseVal.name) do
        if !recNames.contains r then
          recNames := recNames ++ [r]
    -- Constructor dependencies (inductives already marked, so no loop).
    for ctorVal in ctorVals do
      modify fun st => { st with consts := st.consts.insert ctorVal.name }
      dumpDeps ctorVal.type
    let mut recVals : Array RecursorVal := #[]
    for rname in recNames do
      let some recCi := env.find? rname
        | refuse s!"recursor not found: {rname}"
      let .recInfo recVal := recCi
        | refuse s!"expected recursor: {rname}"
      if recVal.isUnsafe then
        refuse s!"unsafe recursor in trusted export: {rname}"
      recVals := recVals.push recVal
    for recVal in recVals do
      modify fun st => { st with consts := st.consts.insert recVal.name }
      dumpDeps recVal.type
    for recVal in recVals do
      for rule in recVal.rules do
        dumpDeps rule.rhs
    let indJson ← indVals.mapM fun val => do
      let ni ← dumpName val.name
      let lp ← dumpUparams val.levelParams
      let ti ← dumpExpr val.type
      let al ← dumpNames val.all
      let cl ← dumpNames val.ctors
      pure (Json.mkObj [("name", ni), ("levelParams", lp), ("type", ti),
        ("numParams", val.numParams), ("numIndices", val.numIndices),
        ("all", al), ("ctors", cl), ("numNested", val.numNested),
        ("isRec", val.isRec), ("isReflexive", val.isReflexive),
        ("isUnsafe", val.isUnsafe)])
    let ctorJson ← ctorVals.mapM fun val => do
      let ni ← dumpName val.name
      let lp ← dumpUparams val.levelParams
      let ti ← dumpExpr val.type
      let ii ← dumpName val.induct
      pure (Json.mkObj [("name", ni), ("levelParams", lp), ("type", ti),
        ("induct", ii), ("cidx", val.cidx), ("numParams", val.numParams),
        ("numFields", val.numFields), ("isUnsafe", val.isUnsafe)])
    let recJson ← recVals.mapM fun val => do
      let ni ← dumpName val.name
      let lp ← dumpUparams val.levelParams
      let ti ← dumpExpr val.type
      let al ← dumpNames val.all
      let rules ← val.rules.mapM dumpRecRule
      pure (Json.mkObj [("name", ni), ("levelParams", lp), ("type", ti),
        ("all", al), ("numParams", val.numParams),
        ("numIndices", val.numIndices), ("numMotives", val.numMotives),
        ("numMinors", val.numMinors), ("rules", rules.toJson),
        ("k", val.k), ("isUnsafe", val.isUnsafe)])
    IO.println ((Json.mkObj [("inductive", .mkObj [("types", indJson.toJson),
      ("ctors", ctorJson.toJson), ("recs", recJson.toJson)])]).compress)
  | .ctorInfo val =>
    dumpConstant val.induct
  | .recInfo val =>
    for indName in val.all do
      dumpConstant indName

end

def metadata : Json :=
  Json.mkObj [
    ("meta", Json.mkObj [
      ("exporter", Json.mkObj [
        ("name", "gaussian-export34"),
        ("version", "1.0.0")]),
      ("lean", Json.mkObj [
        ("version", versionString),
        ("githash", githash)]),
      ("format", Json.mkObj [
        ("version", "3.1.0")])])]

/-- Build the recursor map: inductive name -> recursor names. -/
def addRecs (acc : List (Name × List Name)) (recName : Name)
    (inds : List Name) : List (Name × List Name) :=
  inds.foldl (fun acc ind =>
    match acc.find? (fun p => p.1 == ind) with
    | some _ => acc.map fun p =>
        if p.1 == ind && !p.2.contains recName then
          (p.1, p.2 ++ [recName])
        else p
    | none => acc ++ [(ind, [recName])]) acc

def buildRecMap (env : Environment) : List (Name × List Name) :=
  env.constants.fold (fun acc _ ci => match ci with
    | .recInfo recVal => addRecs acc recVal.name recVal.all
    | _ => acc) []

unsafe def runExport (env : Environment) (roots : List Name) : IO Unit := do
  let init : State := { recMap := buildRecMap env }
  let act : M Unit := do
    IO.println metadata.compress
    for r in roots do
      modify fun st => { st with current := r }
      dumpConstant r
  let _ ← StateT.run (s := init) (ReaderT.run (r := env) act)
  pure ()

unsafe def main (args : List String) : IO Unit := do
  let modIdx : Nat := 0
  if args.length < 3 then
    throw (.userError "usage: export34 <Module> -- <root1> ...")
  let modName := args[modIdx]!.toName
  let roots := (args.drop 2).filter (· != "--") |>.map String.toName
  if roots.isEmpty then
    throw (.userError "no export roots given")
  IO.eprintln s!"export34: module={modName} nroots={roots.length} roots={roots}"
  withImportModules #[{ module := modName }] {} fun env => do
    runExport env roots

end Export34

unsafe def main (args : List String) : IO Unit := Export34.main args
