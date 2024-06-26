import Leanses

namespace LeansesTest.Lens.Test1

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

end LeansesTest.Lens.Test1

namespace LeansesTest.Lens.Test2

-- #eval (fun (x:Fin 5) => if x == 2 then 3 else 4) ^.. traverse_Fin

-- #eval ((gset set_Fin 1 (fun (x:Fin 5) => if x == 2 then 3 else 4))) ^.. traverse_Fin

end LeansesTest.Lens.Test2

namespace LeansesTest.Lens.Test3

structure SubEx (α: Type _) where
  c : List α
  deriving Repr

mklenses SubEx

end LeansesTest.Lens.Test3
