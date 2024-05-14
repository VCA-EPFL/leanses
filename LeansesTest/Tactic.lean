import Leanses

namespace LeansesTest.Tactic.Test1

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

open Leanses

example (str:Example n):
  <{ str with s3 n∘∘c n∘∘fin_at j := "Random" }>^.s3 n∘∘c n∘∘fin_at j = "Random" := by
  simp_lens; rfl

example (str:Example n):
  i = j → <{ str with s2 n := 3, s3 n∘∘c n∘∘fin_at j := "Random" }>^.s3 n∘∘c n∘∘fin_at i = "Random" := by
  intros; subst i; simp_lens; rfl

example (str:Example n):
  i ≠ j → <{ str with s3 n∘∘c n∘∘fin_at j := "Random" }>^.s3 n∘∘c n∘∘fin_at i = str^.s3 n∘∘c n∘∘fin_at i := by
  intros h; simp_lens (discharger := assumption); rfl

end LeansesTest.Tactic.Test1
