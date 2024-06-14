import Lake
open Lake DSL

package «leanses»

@[default_target]
lean_lib «Leanses»

lean_lib «LeansesTest» where
  globs := #[.submodules `LeansesTest]
