import Lake
open Lake DSL

package «Weil_Rep_finitefield» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b2158cc40abd16b858e8aa3b0e6f452789b4b28b"

@[default_target]
lean_lib «WeilRepFinitefield» where
  -- add any library configuration options here
