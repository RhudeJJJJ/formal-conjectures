/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCanonicalTreeCoverage
namespace Gebendorfer.RadenkovicGutman.CanonicalTreeCoverage
open RootedTreeEnumeration
set_option maxHeartbeats 0

def checkRange (n : ℕ) (xs : List (Family n)) (ys : List (Family (n+1)))
    (start count : ℕ) (h : start+count≤xs.length)
    (w : Fin count → Vertices n → Witness (n+1) ys.length) : Bool :=
  decide (∀ i v, acceptsIso (n := n+1)
    (xs.get ⟨start+i.val,by omega⟩,v) (ys.get (w i v).target) (w i v).map=true)

theorem range_sound (n : ℕ) (xs : List (Family n)) (ys : List (Family (n+1)))
    (start count : ℕ) (h : start+count≤xs.length)
    (w : Fin count → Vertices n → Witness (n+1) ys.length)
    (hc : checkRange n xs ys start count h w=true)
    (k : Fin count) (v : Vertices n) (i : Fin xs.length) (hi : start+k.val=i.val) :
    ∃ j : Fin ys.length, ∃ e : graph (n := n+1) (xs.get i,v) ≃g graph (ys.get j),
      e (root (n+1))=root (n+1) := by
  have hki : (⟨start+k.val,by omega⟩ : Fin xs.length)=i := Fin.ext hi
  have hm := of_decide_eq_true hc k v
  rw [← hki]
  exact ⟨(w k v).target,checkedIso _ _ _ hm,checkedIso_root _ _ _ hm⟩

#print axioms range_sound
end Gebendorfer.RadenkovicGutman.CanonicalTreeCoverage
