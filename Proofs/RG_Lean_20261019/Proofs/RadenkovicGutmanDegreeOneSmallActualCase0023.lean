/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0023 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0023 : (Vertices 1 ⊕ Fin 3 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,6,3,4,5,1,0,7,8,9,10,11,12] (sourceLabel 1 2 7 v)
def fusedMap0023 : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 2 7 v)
theorem sourceMap0023_checked : acceptsGraphIso
    (source (graph core0023) (root 1) 2 7) DegreeOneSmallSpectrum858.graph sourceMap0023=true := by decide +kernel
theorem fusedMap0023_checked : acceptsGraphIso
    (fused (graph core0023) (root 1) 2 7) DegreeOneSmallSpectrum861.graph fusedMap0023=true := by decide +kernel
theorem certified0023 : Certified (graph core0023) (root 1) 2 7 :=
  of_native_maps core0023 DegreeOneSmallSpectrum858.graph DegreeOneSmallSpectrum861.graph
    sourceMap0023 fusedMap0023 sourceMap0023_checked fusedMap0023_checked
    DegreeOneSmallComparisons.comparison0023
#print axioms sourceMap0023_checked
#print axioms fusedMap0023_checked
#print axioms certified0023
def sourceMap0023swap : (Vertices 1 ⊕ Fin 8 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,6,1,0,7,8,9,10,11,12,3,4,5] (sourceLabel 1 7 2 v)
def fusedMap0023swap : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 7 2 v)
theorem sourceMap0023swap_checked : acceptsGraphIso
    (source (graph core0023) (root 1) 7 2) DegreeOneSmallSpectrum858.graph sourceMap0023swap=true := by decide +kernel
theorem fusedMap0023swap_checked : acceptsGraphIso
    (fused (graph core0023) (root 1) 7 2) DegreeOneSmallSpectrum861.graph fusedMap0023swap=true := by decide +kernel
theorem certified0023swap : Certified (graph core0023) (root 1) 7 2 :=
  of_native_maps core0023 DegreeOneSmallSpectrum858.graph DegreeOneSmallSpectrum861.graph
    sourceMap0023swap fusedMap0023swap sourceMap0023swap_checked fusedMap0023swap_checked
    DegreeOneSmallComparisons.comparison0023
#print axioms sourceMap0023swap_checked
#print axioms fusedMap0023swap_checked
#print axioms certified0023swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
