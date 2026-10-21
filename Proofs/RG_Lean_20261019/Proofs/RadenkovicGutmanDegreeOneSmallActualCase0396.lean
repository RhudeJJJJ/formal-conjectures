/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0396 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0396 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0396 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0396_checked : acceptsGraphIso
    (source (graph core0396) (root 6) 0 3) DegreeOneSmallSpectrum407.graph sourceMap0396=true := by decide +kernel
theorem fusedMap0396_checked : acceptsGraphIso
    (fused (graph core0396) (root 6) 0 3) DegreeOneSmallSpectrum411.graph fusedMap0396=true := by decide +kernel
theorem certified0396 : Certified (graph core0396) (root 6) 0 3 :=
  of_native_maps core0396 DegreeOneSmallSpectrum407.graph DegreeOneSmallSpectrum411.graph
    sourceMap0396 fusedMap0396 sourceMap0396_checked fusedMap0396_checked
    DegreeOneSmallComparisons.comparison0396
#print axioms sourceMap0396_checked
#print axioms fusedMap0396_checked
#print axioms certified0396
def sourceMap0396swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap0396swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0396swap_checked : acceptsGraphIso
    (source (graph core0396) (root 6) 3 0) DegreeOneSmallSpectrum407.graph sourceMap0396swap=true := by decide +kernel
theorem fusedMap0396swap_checked : acceptsGraphIso
    (fused (graph core0396) (root 6) 3 0) DegreeOneSmallSpectrum411.graph fusedMap0396swap=true := by decide +kernel
theorem certified0396swap : Certified (graph core0396) (root 6) 3 0 :=
  of_native_maps core0396 DegreeOneSmallSpectrum407.graph DegreeOneSmallSpectrum411.graph
    sourceMap0396swap fusedMap0396swap sourceMap0396swap_checked fusedMap0396swap_checked
    DegreeOneSmallComparisons.comparison0396
#print axioms sourceMap0396swap_checked
#print axioms fusedMap0396swap_checked
#print axioms certified0396swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
