/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0162 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0162 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,5,1,2,3,4] (sourceLabel 5 0 3 v)
def fusedMap0162 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0162_checked : acceptsGraphIso
    (source (graph core0162) (root 5) 0 3) DegreeOneSmallSpectrum167.graph sourceMap0162=true := by decide +kernel
theorem fusedMap0162_checked : acceptsGraphIso
    (fused (graph core0162) (root 5) 0 3) DegreeOneSmallSpectrum168.graph fusedMap0162=true := by decide +kernel
theorem certified0162 : Certified (graph core0162) (root 5) 0 3 :=
  of_native_maps core0162 DegreeOneSmallSpectrum167.graph DegreeOneSmallSpectrum168.graph
    sourceMap0162 fusedMap0162 sourceMap0162_checked fusedMap0162_checked
    DegreeOneSmallComparisons.comparison0162
#print axioms sourceMap0162_checked
#print axioms fusedMap0162_checked
#print axioms certified0162
def sourceMap0162swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 5 3 0 v)
def fusedMap0162swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0162swap_checked : acceptsGraphIso
    (source (graph core0162) (root 5) 3 0) DegreeOneSmallSpectrum167.graph sourceMap0162swap=true := by decide +kernel
theorem fusedMap0162swap_checked : acceptsGraphIso
    (fused (graph core0162) (root 5) 3 0) DegreeOneSmallSpectrum168.graph fusedMap0162swap=true := by decide +kernel
theorem certified0162swap : Certified (graph core0162) (root 5) 3 0 :=
  of_native_maps core0162 DegreeOneSmallSpectrum167.graph DegreeOneSmallSpectrum168.graph
    sourceMap0162swap fusedMap0162swap sourceMap0162swap_checked fusedMap0162swap_checked
    DegreeOneSmallComparisons.comparison0162
#print axioms sourceMap0162swap_checked
#print axioms fusedMap0162swap_checked
#print axioms certified0162swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
