/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0590 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0590 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0590 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0590_checked : acceptsGraphIso
    (source (graph core0590) (root 7) 1 2) DegreeOneSmallSpectrum1132.graph sourceMap0590=true := by decide +kernel
theorem fusedMap0590_checked : acceptsGraphIso
    (fused (graph core0590) (root 7) 1 2) DegreeOneSmallSpectrum872.graph fusedMap0590=true := by decide +kernel
theorem certified0590 : Certified (graph core0590) (root 7) 1 2 :=
  of_native_maps core0590 DegreeOneSmallSpectrum1132.graph DegreeOneSmallSpectrum872.graph
    sourceMap0590 fusedMap0590 sourceMap0590_checked fusedMap0590_checked
    DegreeOneSmallComparisons.comparison0590
#print axioms sourceMap0590_checked
#print axioms fusedMap0590_checked
#print axioms certified0590
def sourceMap0590swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0590swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0590swap_checked : acceptsGraphIso
    (source (graph core0590) (root 7) 2 1) DegreeOneSmallSpectrum1132.graph sourceMap0590swap=true := by decide +kernel
theorem fusedMap0590swap_checked : acceptsGraphIso
    (fused (graph core0590) (root 7) 2 1) DegreeOneSmallSpectrum872.graph fusedMap0590swap=true := by decide +kernel
theorem certified0590swap : Certified (graph core0590) (root 7) 2 1 :=
  of_native_maps core0590 DegreeOneSmallSpectrum1132.graph DegreeOneSmallSpectrum872.graph
    sourceMap0590swap fusedMap0590swap sourceMap0590swap_checked fusedMap0590swap_checked
    DegreeOneSmallComparisons.comparison0590
#print axioms sourceMap0590swap_checked
#print axioms fusedMap0590swap_checked
#print axioms certified0590swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
