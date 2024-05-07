import Leanses

namespace Test1

structure SubEx where
  c : String
  deriving Repr

-- `mklenses` automatically generates lenses for a structure.
mklenses SubEx
open SubEx.l

structure Example where
  s1 : String
  s2 : Int
  s3 : SubEx
  deriving Repr

mklenses Example
open Example.l

def v := Example.mk "a" 1 {c := "c"}

-- Structure update syntax built into Lean
/--
info: let __src := v;
{ s1 := "b", s2 := 5, s3 := __src.s3 } : Example
-/
#guard_msgs in
#check { v with s2 := 5, s1 := "b" }

/--
info: let __src := v;
{ s1 := "c", s2 := __src.s2,
  s3 :=
    let __src := __src.s3;
    { c := "deep" } } : Example
-/
#guard_msgs in
#check { v with s3.c := "deep", s1 := "c" }

-- Structure updates using lenses

/--
info: <{ v with s2 := 5, s1 := "b" }> : Example
-/
#guard_msgs in
#check <{ v with s2 := 5, s1 := "b" }>

/--
info: <{ v with s3∘∘c := "deep", s1 := "c" }> : Example
-/
#guard_msgs in
#check <{ v with s3∘∘c := "deep", s1 := "c" }>

set_option pp.hideLensUpdates true

/--
info: <{ v ... }> : Example
-/
#guard_msgs in
#check <{ v with s2 := 5, s1 := "b" }>

/--
info: <{ v ... }> : Example
-/
#guard_msgs in
#check <{ v with s3∘∘c := "deep", s1 := "c" }>

end Test1

namespace Test2

structure SubEx (n : Nat) where
  c : Fin n → String

-- `mklenses` automatically generates lenses for a structure.
mklenses SubEx
open SubEx.l

structure Example (n : Nat) where
  s1 : String
  s2 : Int
  s3 : SubEx n

mklenses Example
open Example.l

example (str:Example n):
  <{ str with s3 n∘∘c n∘∘Leanses.fin_at j := "Random" }>^.s3 n∘∘c n∘∘Leanses.fin_at j = "Random" := by
  simp_lens

example (str:Example n):
  i = j → <{ str with s2 n := 3, s3 n∘∘c n∘∘Leanses.fin_at j := "Random" }>^.s3 n∘∘c n∘∘Leanses.fin_at i = "Random" := by
  simp_lens

example (str:Example n):
  i ≠ j → <{ str with s3 n∘∘c n∘∘Leanses.fin_at j := "Random" }>^.s3 n∘∘c n∘∘Leanses.fin_at i = str^.s3 n∘∘c n∘∘Leanses.fin_at i := by
  simp_lens

end Test2
