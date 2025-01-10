import Lake
open Lake DSL

package «polySat» {
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ],
  -- add any additional package configuration options here
 -- moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  }

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "v0.0.21"
--require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.5.1"


@[default_target]
lean_lib «PolySat» where
  -- add any library configuration options here
