/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0660 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0660 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0660 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0660_checked : acceptsGraphIso
    (source (graph core0660) (root 7) 0 3) DegreeOneSmallSpectrum1485.graph sourceMap0660=true := by decide +kernel
theorem fusedMap0660_checked : acceptsGraphIso
    (fused (graph core0660) (root 7) 0 3) DegreeOneSmallSpectrum947.graph fusedMap0660=true := by decide +kernel
theorem certified0660 : Certified (graph core0660) (root 7) 0 3 :=
  of_native_maps core0660 DegreeOneSmallSpectrum1485.graph DegreeOneSmallSpectrum947.graph
    sourceMap0660 fusedMap0660 sourceMap0660_checked fusedMap0660_checked
    DegreeOneSmallComparisons.comparison0660
#print axioms sourceMap0660_checked
#print axioms fusedMap0660_checked
#print axioms certified0660
def sourceMap0660swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0660swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0660swap_checked : acceptsGraphIso
    (source (graph core0660) (root 7) 3 0) DegreeOneSmallSpectrum1485.graph sourceMap0660swap=true := by decide +kernel
theorem fusedMap0660swap_checked : acceptsGraphIso
    (fused (graph core0660) (root 7) 3 0) DegreeOneSmallSpectrum947.graph fusedMap0660swap=true := by decide +kernel
theorem certified0660swap : Certified (graph core0660) (root 7) 3 0 :=
  of_native_maps core0660 DegreeOneSmallSpectrum1485.graph DegreeOneSmallSpectrum947.graph
    sourceMap0660swap fusedMap0660swap sourceMap0660swap_checked fusedMap0660swap_checked
    DegreeOneSmallComparisons.comparison0660
#print axioms sourceMap0660swap_checked
#print axioms fusedMap0660swap_checked
#print axioms certified0660swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
