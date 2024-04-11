import Lake
open Lake DSL

require aesop from git
  "https://github.com/leanprover-community/aesop.git"

package «leanses»

@[default_target]
lean_lib «Leanses»

lean_lib «LeansesTest» where
  globs := #[.submodules `LeansesTest]
