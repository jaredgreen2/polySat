import Lake
open Lake DSL

package «polySat» {
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ],
  -- add any additional package configuration options here
  }

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "v0.0.8"

@[default_target]
lean_lib «PolySat» where
  -- add any library configuration options here
