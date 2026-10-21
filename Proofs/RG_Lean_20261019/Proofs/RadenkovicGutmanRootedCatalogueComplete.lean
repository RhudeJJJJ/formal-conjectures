/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueStep00
import Proofs.RadenkovicGutmanRootedCatalogueStep01
import Proofs.RadenkovicGutmanRootedCatalogueStep02
import Proofs.RadenkovicGutmanRootedCatalogueStep03
import Proofs.RadenkovicGutmanRootedCatalogueStep04
import Proofs.RadenkovicGutmanRootedCatalogueStep05
import Proofs.RadenkovicGutmanRootedCatalogueStep06
import Proofs.RadenkovicGutmanRootedCatalogueStep07
import Proofs.RadenkovicGutmanRootedCatalogueStep08
import Proofs.RadenkovicGutmanRootedCatalogueStep09

namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
theorem singleton_covered : ∃ i : Fin (catalogue 0).length, (catalogue 0).get i=() :=
  ⟨⟨0,by decide⟩,rfl⟩
theorem all_steps : ∀ n, n < 10 → ∀ i : Fin (catalogue n).length, ∀ v : Vertices n,
    ∃ j : Fin (catalogue (n+1)).length,
      ∃ e : graph (n := n+1) ((catalogue n).get i,v) ≃g graph ((catalogue (n+1)).get j),
        e (root (n+1))=root (n+1) := by
  intro n hn
  interval_cases n
  · exact step_sound 0 level0 level1 witnesses0 step0
  · exact step_sound 1 level1 level2 witnesses1 step1
  · exact step_sound 2 level2 level3 witnesses2 step2
  · exact step_sound 3 level3 level4 witnesses3 step3
  · exact step_sound 4 level4 level5 witnesses4 step4
  · exact step_sound 5 level5 level6 witnesses5 step5
  · exact step_sound 6 level6 level7 witnesses6 step6
  · exact step_sound 7 level7 level8 witnesses7 step7
  · exact step_sound 8 level8 level9 witnesses8 step8
  · exact step_sound 9 level9 level10 witnesses9 step9
theorem all_actual_trees {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (hG : G.IsTree) (n : ℕ) (hn : n≤10)
    (hc : Fintype.card V=n+1) :
    ∃ i : Fin (catalogue n).length, ∃ e : G ≃g graph ((catalogue n).get i), e r=root n :=
  actual_tree_covered catalogue 10 singleton_covered all_steps G r hG n hn hc
#print axioms all_steps
#print axioms all_actual_trees
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
