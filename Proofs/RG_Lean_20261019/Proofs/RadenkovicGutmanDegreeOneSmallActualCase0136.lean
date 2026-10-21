/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0136 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0136 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 1 3 v)
def fusedMap0136 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 1 3 v)
theorem sourceMap0136_checked : acceptsGraphIso
    (source (graph core0136) (root 4) 1 3) DegreeOneSmallSpectrum208.graph sourceMap0136=true := by decide +kernel
theorem fusedMap0136_checked : acceptsGraphIso
    (fused (graph core0136) (root 4) 1 3) DegreeOneSmallSpectrum165.graph fusedMap0136=true := by decide +kernel
theorem certified0136 : Certified (graph core0136) (root 4) 1 3 :=
  of_native_maps core0136 DegreeOneSmallSpectrum208.graph DegreeOneSmallSpectrum165.graph
    sourceMap0136 fusedMap0136 sourceMap0136_checked fusedMap0136_checked
    DegreeOneSmallComparisons.comparison0136
#print axioms sourceMap0136_checked
#print axioms fusedMap0136_checked
#print axioms certified0136
def sourceMap0136swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6] (sourceLabel 4 3 1 v)
def fusedMap0136swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 3 1 v)
theorem sourceMap0136swap_checked : acceptsGraphIso
    (source (graph core0136) (root 4) 3 1) DegreeOneSmallSpectrum208.graph sourceMap0136swap=true := by decide +kernel
theorem fusedMap0136swap_checked : acceptsGraphIso
    (fused (graph core0136) (root 4) 3 1) DegreeOneSmallSpectrum165.graph fusedMap0136swap=true := by decide +kernel
theorem certified0136swap : Certified (graph core0136) (root 4) 3 1 :=
  of_native_maps core0136 DegreeOneSmallSpectrum208.graph DegreeOneSmallSpectrum165.graph
    sourceMap0136swap fusedMap0136swap sourceMap0136swap_checked fusedMap0136swap_checked
    DegreeOneSmallComparisons.comparison0136
#print axioms sourceMap0136swap_checked
#print axioms fusedMap0136swap_checked
#print axioms certified0136swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
