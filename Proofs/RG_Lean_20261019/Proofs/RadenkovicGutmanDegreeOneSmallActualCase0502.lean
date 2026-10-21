/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0502 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0502 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,10,9,7,8] (sourceLabel 7 0 1 v)
def fusedMap0502 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (fusedLabel 7 0 1 v)
theorem sourceMap0502_checked : acceptsGraphIso
    (source (graph core0502) (root 7) 0 1) DegreeOneSmallSpectrum192.graph sourceMap0502=true := by decide +kernel
theorem fusedMap0502_checked : acceptsGraphIso
    (fused (graph core0502) (root 7) 0 1) DegreeOneSmallSpectrum197.graph fusedMap0502=true := by decide +kernel
theorem certified0502 : Certified (graph core0502) (root 7) 0 1 :=
  of_native_maps core0502 DegreeOneSmallSpectrum192.graph DegreeOneSmallSpectrum197.graph
    sourceMap0502 fusedMap0502 sourceMap0502_checked fusedMap0502_checked
    DegreeOneSmallComparisons.comparison0502
#print axioms sourceMap0502_checked
#print axioms fusedMap0502_checked
#print axioms certified0502
def sourceMap0502swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,10,7,8,9] (sourceLabel 7 1 0 v)
def fusedMap0502swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (fusedLabel 7 1 0 v)
theorem sourceMap0502swap_checked : acceptsGraphIso
    (source (graph core0502) (root 7) 1 0) DegreeOneSmallSpectrum192.graph sourceMap0502swap=true := by decide +kernel
theorem fusedMap0502swap_checked : acceptsGraphIso
    (fused (graph core0502) (root 7) 1 0) DegreeOneSmallSpectrum197.graph fusedMap0502swap=true := by decide +kernel
theorem certified0502swap : Certified (graph core0502) (root 7) 1 0 :=
  of_native_maps core0502 DegreeOneSmallSpectrum192.graph DegreeOneSmallSpectrum197.graph
    sourceMap0502swap fusedMap0502swap sourceMap0502swap_checked fusedMap0502swap_checked
    DegreeOneSmallComparisons.comparison0502
#print axioms sourceMap0502swap_checked
#print axioms fusedMap0502swap_checked
#print axioms certified0502swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
