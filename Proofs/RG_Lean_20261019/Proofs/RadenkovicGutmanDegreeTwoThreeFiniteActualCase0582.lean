/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0582 : Family 10 := level10.get ⟨646,by decide⟩
def sourceMap0582 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0582 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0582_checked : acceptsGraphIso
    (source (graph core0582) (root 10) 0 0) DegreeOneSmallSpectrum1650.graph sourceMap0582=true := by decide +kernel
theorem fusedMap0582_checked : acceptsGraphIso
    (fused (graph core0582) (root 10) 0 0) DegreeOneSmallSpectrum1236.graph fusedMap0582=true := by decide +kernel
theorem certified0582 : Certified (graph core0582) (root 10) 0 0 :=
  of_native_maps core0582 DegreeOneSmallSpectrum1650.graph DegreeOneSmallSpectrum1236.graph
    sourceMap0582 fusedMap0582 sourceMap0582_checked fusedMap0582_checked
    DegreeTwoThreeFiniteComparisons.comparison0582
#print axioms sourceMap0582_checked
#print axioms fusedMap0582_checked
#print axioms certified0582
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
