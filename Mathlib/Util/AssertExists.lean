/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import Mathlib.Init
import Lean.Elab.Command
import Mathlib.Util.AssertExistsExt

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## TODO

Potentially after the port reimplement the mathlib 3 linters to check that declarations asserted
about do eventually exist.

Implement `assert_instance` and `assert_no_instance`
-/

section
open Lean Elab Meta Command

namespace Mathlib.AssertNotExist

open Lean Elab Command
/-- `#check_assertions` retrieves all declarations and all imports that were declared
not to exist so far (including in transitively imported files) and reports their current
status:
* ✓ means the declaration or import exists,
* × means the declaration or import does not exist.

This means that the expectation is that all checks *succeed* by the time `#check_assertions`
is used, typically once all of `Mathlib` has been built.

If all declarations and imports are available when `#check_assertions` is used,
then the command logs an info. Otherwise, it emits a warning.
-/
elab "#check_assertions" : command => do
  let env ← getEnv
  let ext := assertExistsExt.getState env
  if ext.isEmpty then logInfo "No assertions made." else
  let allMods := env.allImportedModuleNames
  let mut msgs := #[m!""]
  let mut outcome := m!""
  let mut (allExist?, cond) := (true, false)
  for d in ext.toArray.qsort fun d e =>
    (e.isDecl ≤ d.isDecl) && (d.givenName.toString < e.givenName.toString) do
    let type := if d.isDecl then "declaration" else "module"
    if d.isDecl then
      cond := env.contains d.givenName
    else
      cond := allMods.contains d.givenName
    outcome := if cond then m!"{checkEmoji}" else m!"{crossEmoji}"
    allExist? := allExist? && cond
    msgs := msgs.push m!"{outcome} '{d.givenName}' ({type}) asserted in '{d.modName}'."
  msgs := msgs.push m!"---"
    |>.push m!"{checkEmoji} means the declaration or import exists."
    |>.push m!"{crossEmoji} means the declaration or import does not exist."
  let msg := MessageData.joinSep msgs.toList "\n"
  if allExist? then
    logInfo msg
  else
    logWarning msg

/--
`addDeclEntry isDecl declName` takes as input the `Bool`ean `isDecl` and the `Name` `declName`.
It extends the `AssertExists` environment extension with the data
`isDecl, declName, currentModuleName`.
This information is used to capture declarations and modules that are required to not
exist/be imported at some point, but should eventually exist/be imported.
-/
def addDeclEntry (isDecl : Bool) (declName : Name) : CommandElabM Unit := do
  let modName ← getMainModule
  modifyEnv fun env =>
    assertExistsExt.addEntry env
      { isDecl := isDecl, givenName := declName, modName := modName }

end Mathlib.AssertNotExist

/--
`assert_exists n` is a user command that asserts that a declaration named `n` exists
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).
-/
elab "assert_exists " n:ident : command => do
  -- this throws an error if the user types something ambiguous or
  -- something that doesn't exist, otherwise succeeds
  let _ ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n

/--
`assert_not_exists n` is a user command that asserts that a declaration named `n` *does not exist*
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.

`assert_not_exists` statements should generally live at the top of the file, after the module doc.
-/
elab "assert_not_exists " n:ident : command => do
  let decl ← ((liftCoreM <| realizeGlobalConstNoOverloadWithInfo n) <|> return .anonymous)
  if decl == .anonymous then
    Mathlib.AssertNotExist.addDeclEntry true n.getId
  else
  let env ← getEnv
  let c ← mkConstWithLevelParams decl
  let msg ← (do
    let mut some idx := env.getModuleIdxFor? decl
      | pure m!"Declaration {c} is defined in this file."
    let mut msg := m!"Declaration {c} is not allowed to be imported by this file.\n\
      It is defined in {env.header.moduleNames[idx.toNat]!},"
    for i in [idx.toNat+1:env.header.moduleData.size] do
      if env.header.moduleData[i]!.imports.any (·.module == env.header.moduleNames[idx.toNat]!) then
        idx := i
        msg := msg ++ m!"\n  which is imported by {env.header.moduleNames[i]!},"
    pure <| msg ++ m!"\n  which is imported by this file.")
  throw <| .error n m!"{msg}\n\n\
    These invariants are maintained by `assert_not_exists` statements, \
    and exist in order to ensure that \"complicated\" parts of the library \
    are not accidentally introduced as dependencies of \"simple\" parts of the library."

/-- `assert_not_imported m₁ m₂ ... mₙ` checks that each one of the modules `m₁ m₂ ... mₙ` is not
among the transitive imports of the current file.

The command does not currently check whether the modules `m₁ m₂ ... mₙ` actually exist.
-/
-- TODO: make sure that each one of `m₁ m₂ ... mₙ` is the name of an actually existing module!
elab "assert_not_imported " ids:ident+ : command => do
  let mods := (← getEnv).allImportedModuleNames
  for id in ids do
    if mods.contains id.getId then
      logWarningAt id m!"the module '{id}' is (transitively) imported"
    else
      Mathlib.AssertNotExist.addDeclEntry false id.getId

end
