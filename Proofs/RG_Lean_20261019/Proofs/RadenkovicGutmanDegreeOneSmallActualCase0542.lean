/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0542 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0542 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0542 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0542_checked : acceptsGraphIso
    (source (graph core0542) (root 7) 1 2) DegreeOneSmallSpectrum1488.graph sourceMap0542=true := by decide +kernel
theorem fusedMap0542_checked : acceptsGraphIso
    (fused (graph core0542) (root 7) 1 2) DegreeOneSmallSpectrum956.graph fusedMap0542=true := by decide +kernel
theorem certified0542 : Certified (graph core0542) (root 7) 1 2 :=
  of_native_maps core0542 DegreeOneSmallSpectrum1488.graph DegreeOneSmallSpectrum956.graph
    sourceMap0542 fusedMap0542 sourceMap0542_checked fusedMap0542_checked
    DegreeOneSmallComparisons.comparison0542
#print axioms sourceMap0542_checked
#print axioms fusedMap0542_checked
#print axioms certified0542
def sourceMap0542swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0542swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0542swap_checked : acceptsGraphIso
    (source (graph core0542) (root 7) 2 1) DegreeOneSmallSpectrum1488.graph sourceMap0542swap=true := by decide +kernel
theorem fusedMap0542swap_checked : acceptsGraphIso
    (fused (graph core0542) (root 7) 2 1) DegreeOneSmallSpectrum956.graph fusedMap0542swap=true := by decide +kernel
theorem certified0542swap : Certified (graph core0542) (root 7) 2 1 :=
  of_native_maps core0542 DegreeOneSmallSpectrum1488.graph DegreeOneSmallSpectrum956.graph
    sourceMap0542swap fusedMap0542swap sourceMap0542swap_checked fusedMap0542swap_checked
    DegreeOneSmallComparisons.comparison0542
#print axioms sourceMap0542swap_checked
#print axioms fusedMap0542swap_checked
#print axioms certified0542swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
