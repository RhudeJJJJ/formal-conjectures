/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0582 : Family 7 := level7.get ⟨30,by decide⟩
def sourceMap0582 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0582 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0582_checked : acceptsGraphIso
    (source (graph core0582) (root 7) 0 3) DegreeOneSmallSpectrum1112.graph sourceMap0582=true := by decide +kernel
theorem fusedMap0582_checked : acceptsGraphIso
    (fused (graph core0582) (root 7) 0 3) DegreeOneSmallSpectrum871.graph fusedMap0582=true := by decide +kernel
theorem certified0582 : Certified (graph core0582) (root 7) 0 3 :=
  of_native_maps core0582 DegreeOneSmallSpectrum1112.graph DegreeOneSmallSpectrum871.graph
    sourceMap0582 fusedMap0582 sourceMap0582_checked fusedMap0582_checked
    DegreeOneSmallComparisons.comparison0582
#print axioms sourceMap0582_checked
#print axioms fusedMap0582_checked
#print axioms certified0582
def sourceMap0582swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0582swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0582swap_checked : acceptsGraphIso
    (source (graph core0582) (root 7) 3 0) DegreeOneSmallSpectrum1112.graph sourceMap0582swap=true := by decide +kernel
theorem fusedMap0582swap_checked : acceptsGraphIso
    (fused (graph core0582) (root 7) 3 0) DegreeOneSmallSpectrum871.graph fusedMap0582swap=true := by decide +kernel
theorem certified0582swap : Certified (graph core0582) (root 7) 3 0 :=
  of_native_maps core0582 DegreeOneSmallSpectrum1112.graph DegreeOneSmallSpectrum871.graph
    sourceMap0582swap fusedMap0582swap sourceMap0582swap_checked fusedMap0582swap_checked
    DegreeOneSmallComparisons.comparison0582
#print axioms sourceMap0582swap_checked
#print axioms fusedMap0582swap_checked
#print axioms certified0582swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
