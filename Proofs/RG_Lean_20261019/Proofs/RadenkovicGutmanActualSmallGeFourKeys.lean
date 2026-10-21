/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanFiniteTreeTransfer
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Key where
  n : ℕ
  index : ℕ
  p : ℕ
  q : ℕ
  deriving DecidableEq

def fallback : (n : ℕ) → Family n
  | 0 => ()
  | n+1 => (fallback n,root n)

def representative (n i : ℕ) : Family n :=
  (RootedCatalogueData.catalogue n).getD i (fallback n)

theorem getD_fin {A : Type} (xs : List A) (d : A) :
    ∀ i : Fin xs.length, xs.getD i.val d=xs.get i := by
  induction xs with
  | nil => intro i; exact Fin.elim0 i
  | cons x xs ih =>
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    exact ih j

theorem representative_get (n : ℕ) (i : Fin (RootedCatalogueData.catalogue n).length) :
    representative n i.val=(RootedCatalogueData.catalogue n).get i :=
  getD_fin _ _ i

def rootDegree {n : ℕ} (t : Family n) : ℕ :=
  ∑ v : Vertices n, if (graph t).Adj (root n) v then 1 else 0

theorem rootDegree_eq_degree {n : ℕ} (t : Family n) :
    rootDegree t=(graph t).degree (root n) := by
  exact ((graph t).degree_eq_sum_if_adj (R := ℕ) (root n)).symm

def eligible (n i p q : ℕ) : Bool :=
  decide (n+p+q+3≤12) && decide (4≤rootDegree (representative n i))

noncomputable def Certified (k : Key) : Prop :=
  FiniteTreeTransfer.Certified (graph (representative k.n k.index)) (root k.n) k.p k.q

theorem certified_cons {x : Key} {xs : List Key} (hx : Certified x)
    (hxs : ∀ k ∈ xs, Certified k) : ∀ k ∈ x::xs, Certified k := by
  intro k hk
  rcases List.mem_cons.mp hk with h | h
  · subst k; exact hx
  · exact hxs k h

#print axioms getD_fin
#print axioms representative_get
#print axioms rootDegree_eq_degree
#print axioms certified_cons
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
