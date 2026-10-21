/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0530 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0530 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,10,11,7,8,9] (sourceLabel 7 1 2 v)
def fusedMap0530 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0530_checked : acceptsGraphIso
    (source (graph core0530) (root 7) 1 2) DegreeOneSmallSpectrum1446.graph sourceMap0530=true := by decide +kernel
theorem fusedMap0530_checked : acceptsGraphIso
    (fused (graph core0530) (root 7) 1 2) DegreeOneSmallSpectrum935.graph fusedMap0530=true := by decide +kernel
theorem certified0530 : Certified (graph core0530) (root 7) 1 2 :=
  of_native_maps core0530 DegreeOneSmallSpectrum1446.graph DegreeOneSmallSpectrum935.graph
    sourceMap0530 fusedMap0530 sourceMap0530_checked fusedMap0530_checked
    DegreeOneSmallComparisons.comparison0530
#print axioms sourceMap0530_checked
#print axioms fusedMap0530_checked
#print axioms certified0530
def sourceMap0530swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (sourceLabel 7 2 1 v)
def fusedMap0530swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0530swap_checked : acceptsGraphIso
    (source (graph core0530) (root 7) 2 1) DegreeOneSmallSpectrum1446.graph sourceMap0530swap=true := by decide +kernel
theorem fusedMap0530swap_checked : acceptsGraphIso
    (fused (graph core0530) (root 7) 2 1) DegreeOneSmallSpectrum935.graph fusedMap0530swap=true := by decide +kernel
theorem certified0530swap : Certified (graph core0530) (root 7) 2 1 :=
  of_native_maps core0530 DegreeOneSmallSpectrum1446.graph DegreeOneSmallSpectrum935.graph
    sourceMap0530swap fusedMap0530swap sourceMap0530swap_checked fusedMap0530swap_checked
    DegreeOneSmallComparisons.comparison0530
#print axioms sourceMap0530swap_checked
#print axioms fusedMap0530swap_checked
#print axioms certified0530swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
