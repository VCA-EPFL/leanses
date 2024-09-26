/-
Copyright (c) 2024 Yann Herklotz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Leanses.UniverseLens

set_option autoImplicit true

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

-- /--
-- info: <{ v ... }> : Example
-- -/
-- #guard_msgs in
-- #check <{ v with s2 := 5, s1 := "b" }>

-- /--
-- info: <{ v ... }> : Example
-- -/
-- #guard_msgs in
-- #check <{ v with s3∘∘c := "deep", s1 := "c" }>

end LeansesTest.Lens.Test1

namespace LeansesTest.Lens.Test2

-- #eval (fun (x:Fin 5) => if x == 2 then 3 else 4) ^.. traverse_Fin

-- #eval ((gset set_Fin 1 (fun (x:Fin 5) => if x == 2 then 3 else 4))) ^.. traverse_Fin

end LeansesTest.Lens.Test2

namespace LeansesTest.Lens.Test3

structure SubEx (α: Type _) where
  c : List α
  deriving Repr

open Leanses.UniverseLens

mklenses SubEx

end LeansesTest.Lens.Test3

namespace LeansesTest.Lens.Test4

structure SubEx (α: Type _) where
  c1 : List α
  c2 : List α
  c3 : List α
  c4 : List α
  c5 : List α
  c6 : List α
  c7 : List α
  c8 : List α
  c9 : List α
  c10 : List α
  c11 : List α
  c12 : List α
  c13 : List α
  c14 : List α
  c15 : List α
  c16 : List α
  c17 : List α
  c18 : List α
  c19 : List α
  c20 : List α
  c21 : List α
  c22 : List α
  c23 : List α
  c24 : List α
  c25 : List α
  c26 : List α
  c27 : List α
  c28 : List α
  c29 : List α
  c30 : List α
  deriving Repr

mklenses SubEx

end LeansesTest.Lens.Test4

set_option autoImplicit false
