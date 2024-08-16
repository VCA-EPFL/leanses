import Lake
open Lake DSL

package «leanses»

@[default_target]
lean_lib «Leanses»

@[test_driver]
lean_lib «LeansesTest» where
  globs := #[.submodules `LeansesTest]
