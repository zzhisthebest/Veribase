import Lake
open Lake DSL

package «veribase» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from git "https://github.com/leanprover-community/batteries.git" @ "v4.18.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.18.0"

require plausible from git "https://github.com/leanprover-community/plausible.git" @ "v4.18.0"


@[default_target]
lean_lib «general» where
  -- add any library configuration options here

lean_lib «verina» where
lean_lib «fvapps» where
lean_lib «vericontest» where

lean_exe «extract_decls» where
  root := `scripts.extract_decls
  supportInterpreter := true

lean_exe «tpl_index» where
  root := `scripts.tpl_index
  supportInterpreter := true
