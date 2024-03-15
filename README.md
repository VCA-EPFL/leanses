# Leanses library

Lens implementation for Lean with custom update notation and pretty-printing.
Updates can also be hidden using `pp.hideLensUpdates`.  Using lenses provides a
more flexible record update syntax that can be manipulated to provide better
pretty-printing of such updates.

```lean
structure SubEx where
  c : String
  deriving Repr

-- `mklenses` automatically generates lenses for a structure.
mklenses SubEx

structure Example where
  s1 : String
  s2 : Int
  s3 : SubEx
  deriving Repr

mklenses Example

def v := Example.mk "a" 1 {c := "c"}

-- Structure update syntax built into Lean
#check { v with s2 := 5, s1 := "b" }
---> let src := v;
---> { s1 := "b", s2 := 5, s3 := src.s3 } : Example
#check { v with s3.c := "deep", s1 := "c" }
---> let src := v;
---> { s1 := "c", s2 := src.s2,
--->   s3 :=
--->     let src := src.s3;
--->     { c := "deep" } } : Example

-- Structure updates using lenses
#check <{ v with s2 := 5, s1 := "b" }>
---> <{ v with s2 := 5, s1 := "b" }> : Example
#check <{ v with s3 ∘ c := "deep", s1 := "c" }>
---> <{ v with s3 ∘ c := "deep", s1 := "c" }> : Example

set_option pp.hideLensUpdates true

#check <{ v with s2 := 5, s1 := "b" }>
---> <{ v ... }> : Example
#check <{ v with s3 ∘ c := "deep", s1 := "c" }>
---> <{ v ... }> : Example
```

## Why lenses
