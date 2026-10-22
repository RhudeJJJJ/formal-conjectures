/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0677 : Family 10 := level10.get ⟨906,by decide⟩
def sourceMap0677 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0677 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0677_checked : acceptsGraphIso
    (source (graph core0677) (root 10) 0 0) DegreeOneSmallSpectrum1369.graph sourceMap0677=true := by decide +kernel
theorem fusedMap0677_checked : acceptsGraphIso
    (fused (graph core0677) (root 10) 0 0) DegreeOneSmallSpectrum1318.graph fusedMap0677=true := by decide +kernel
theorem certified0677 : Certified (graph core0677) (root 10) 0 0 :=
  of_native_maps core0677 DegreeOneSmallSpectrum1369.graph DegreeOneSmallSpectrum1318.graph
    sourceMap0677 fusedMap0677 sourceMap0677_checked fusedMap0677_checked
    DegreeTwoThreeFiniteComparisons.comparison0677
#print axioms sourceMap0677_checked
#print axioms fusedMap0677_checked
#print axioms certified0677
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
