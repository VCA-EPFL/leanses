import Lake
open Lake DSL

require aesop from git
  "https://github.com/leanprover-community/aesop.git"

package «leanses» where
  -- add package configuration options here

@[default_target]
lean_lib «Leanses» where
  -- add library configuration options here
