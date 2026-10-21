/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0506 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0506 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,10,11,7,8,9] (sourceLabel 7 1 2 v)
def fusedMap0506 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0506_checked : acceptsGraphIso
    (source (graph core0506) (root 7) 1 2) DegreeOneSmallSpectrum1282.graph sourceMap0506=true := by decide +kernel
theorem fusedMap0506_checked : acceptsGraphIso
    (fused (graph core0506) (root 7) 1 2) DegreeOneSmallSpectrum894.graph fusedMap0506=true := by decide +kernel
theorem certified0506 : Certified (graph core0506) (root 7) 1 2 :=
  of_native_maps core0506 DegreeOneSmallSpectrum1282.graph DegreeOneSmallSpectrum894.graph
    sourceMap0506 fusedMap0506 sourceMap0506_checked fusedMap0506_checked
    DegreeOneSmallComparisons.comparison0506
#print axioms sourceMap0506_checked
#print axioms fusedMap0506_checked
#print axioms certified0506
def sourceMap0506swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (sourceLabel 7 2 1 v)
def fusedMap0506swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0506swap_checked : acceptsGraphIso
    (source (graph core0506) (root 7) 2 1) DegreeOneSmallSpectrum1282.graph sourceMap0506swap=true := by decide +kernel
theorem fusedMap0506swap_checked : acceptsGraphIso
    (fused (graph core0506) (root 7) 2 1) DegreeOneSmallSpectrum894.graph fusedMap0506swap=true := by decide +kernel
theorem certified0506swap : Certified (graph core0506) (root 7) 2 1 :=
  of_native_maps core0506 DegreeOneSmallSpectrum1282.graph DegreeOneSmallSpectrum894.graph
    sourceMap0506swap fusedMap0506swap sourceMap0506swap_checked fusedMap0506swap_checked
    DegreeOneSmallComparisons.comparison0506
#print axioms sourceMap0506swap_checked
#print axioms fusedMap0506swap_checked
#print axioms certified0506swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
