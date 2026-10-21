/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0650 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0650 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0650 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0650_checked : acceptsGraphIso
    (source (graph core0650) (root 7) 1 2) DegreeOneSmallSpectrum1460.graph sourceMap0650=true := by decide +kernel
theorem fusedMap0650_checked : acceptsGraphIso
    (fused (graph core0650) (root 7) 1 2) DegreeOneSmallSpectrum945.graph fusedMap0650=true := by decide +kernel
theorem certified0650 : Certified (graph core0650) (root 7) 1 2 :=
  of_native_maps core0650 DegreeOneSmallSpectrum1460.graph DegreeOneSmallSpectrum945.graph
    sourceMap0650 fusedMap0650 sourceMap0650_checked fusedMap0650_checked
    DegreeOneSmallComparisons.comparison0650
#print axioms sourceMap0650_checked
#print axioms fusedMap0650_checked
#print axioms certified0650
def sourceMap0650swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0650swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0650swap_checked : acceptsGraphIso
    (source (graph core0650) (root 7) 2 1) DegreeOneSmallSpectrum1460.graph sourceMap0650swap=true := by decide +kernel
theorem fusedMap0650swap_checked : acceptsGraphIso
    (fused (graph core0650) (root 7) 2 1) DegreeOneSmallSpectrum945.graph fusedMap0650swap=true := by decide +kernel
theorem certified0650swap : Certified (graph core0650) (root 7) 2 1 :=
  of_native_maps core0650 DegreeOneSmallSpectrum1460.graph DegreeOneSmallSpectrum945.graph
    sourceMap0650swap fusedMap0650swap sourceMap0650swap_checked fusedMap0650swap_checked
    DegreeOneSmallComparisons.comparison0650
#print axioms sourceMap0650swap_checked
#print axioms fusedMap0650swap_checked
#print axioms certified0650swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
