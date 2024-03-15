# Leanses library

Lens implementation for Lean with custom update notation and pretty-printing.
Updates can also be hiddent using `pp.hideLensUpdates`.

```lean
structure SubEx where
  c : String
  deriving Repr

mklenses SubEx

structure Example where
  s1 : String
  s2 : Int
  s3 : SubEx
  deriving Repr

mklenses Example

def v := Example.mk "a" 1 {c := "c"}

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
