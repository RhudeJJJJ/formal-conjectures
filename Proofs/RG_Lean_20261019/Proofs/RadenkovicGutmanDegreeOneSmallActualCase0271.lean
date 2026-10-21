/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0271 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0271 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,6,1,2,3,4,5] (sourceLabel 6 0 4 v)
def fusedMap0271 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0271_checked : acceptsGraphIso
    (source (graph core0271) (root 6) 0 4) DegreeOneSmallSpectrum860.graph sourceMap0271=true := by decide +kernel
theorem fusedMap0271_checked : acceptsGraphIso
    (fused (graph core0271) (root 6) 0 4) DegreeOneSmallSpectrum861.graph fusedMap0271=true := by decide +kernel
theorem certified0271 : Certified (graph core0271) (root 6) 0 4 :=
  of_native_maps core0271 DegreeOneSmallSpectrum860.graph DegreeOneSmallSpectrum861.graph
    sourceMap0271 fusedMap0271 sourceMap0271_checked fusedMap0271_checked
    DegreeOneSmallComparisons.comparison0271
#print axioms sourceMap0271_checked
#print axioms fusedMap0271_checked
#print axioms certified0271
def sourceMap0271swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 4 0 v)
def fusedMap0271swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0271swap_checked : acceptsGraphIso
    (source (graph core0271) (root 6) 4 0) DegreeOneSmallSpectrum860.graph sourceMap0271swap=true := by decide +kernel
theorem fusedMap0271swap_checked : acceptsGraphIso
    (fused (graph core0271) (root 6) 4 0) DegreeOneSmallSpectrum861.graph fusedMap0271swap=true := by decide +kernel
theorem certified0271swap : Certified (graph core0271) (root 6) 4 0 :=
  of_native_maps core0271 DegreeOneSmallSpectrum860.graph DegreeOneSmallSpectrum861.graph
    sourceMap0271swap fusedMap0271swap sourceMap0271swap_checked fusedMap0271swap_checked
    DegreeOneSmallComparisons.comparison0271
#print axioms sourceMap0271swap_checked
#print axioms fusedMap0271swap_checked
#print axioms certified0271swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
