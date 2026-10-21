/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0712 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0712 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0712 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0712_checked : acceptsGraphIso
    (source (graph core0712) (root 7) 0 1) DegreeOneSmallSpectrum317.graph sourceMap0712=true := by decide +kernel
theorem fusedMap0712_checked : acceptsGraphIso
    (fused (graph core0712) (root 7) 0 1) DegreeOneSmallSpectrum318.graph fusedMap0712=true := by decide +kernel
theorem certified0712 : Certified (graph core0712) (root 7) 0 1 :=
  of_native_maps core0712 DegreeOneSmallSpectrum317.graph DegreeOneSmallSpectrum318.graph
    sourceMap0712 fusedMap0712 sourceMap0712_checked fusedMap0712_checked
    DegreeOneSmallComparisons.comparison0712
#print axioms sourceMap0712_checked
#print axioms fusedMap0712_checked
#print axioms certified0712
def sourceMap0712swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0712swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0712swap_checked : acceptsGraphIso
    (source (graph core0712) (root 7) 1 0) DegreeOneSmallSpectrum317.graph sourceMap0712swap=true := by decide +kernel
theorem fusedMap0712swap_checked : acceptsGraphIso
    (fused (graph core0712) (root 7) 1 0) DegreeOneSmallSpectrum318.graph fusedMap0712swap=true := by decide +kernel
theorem certified0712swap : Certified (graph core0712) (root 7) 1 0 :=
  of_native_maps core0712 DegreeOneSmallSpectrum317.graph DegreeOneSmallSpectrum318.graph
    sourceMap0712swap fusedMap0712swap sourceMap0712swap_checked fusedMap0712swap_checked
    DegreeOneSmallComparisons.comparison0712
#print axioms sourceMap0712swap_checked
#print axioms fusedMap0712swap_checked
#print axioms certified0712swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
