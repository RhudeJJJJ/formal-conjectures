/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0648 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0648 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0648 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0648_checked : acceptsGraphIso
    (source (graph core0648) (root 7) 0 3) DegreeOneSmallSpectrum1463.graph sourceMap0648=true := by decide +kernel
theorem fusedMap0648_checked : acceptsGraphIso
    (fused (graph core0648) (root 7) 0 3) DegreeOneSmallSpectrum945.graph fusedMap0648=true := by decide +kernel
theorem certified0648 : Certified (graph core0648) (root 7) 0 3 :=
  of_native_maps core0648 DegreeOneSmallSpectrum1463.graph DegreeOneSmallSpectrum945.graph
    sourceMap0648 fusedMap0648 sourceMap0648_checked fusedMap0648_checked
    DegreeOneSmallComparisons.comparison0648
#print axioms sourceMap0648_checked
#print axioms fusedMap0648_checked
#print axioms certified0648
def sourceMap0648swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0648swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0648swap_checked : acceptsGraphIso
    (source (graph core0648) (root 7) 3 0) DegreeOneSmallSpectrum1463.graph sourceMap0648swap=true := by decide +kernel
theorem fusedMap0648swap_checked : acceptsGraphIso
    (fused (graph core0648) (root 7) 3 0) DegreeOneSmallSpectrum945.graph fusedMap0648swap=true := by decide +kernel
theorem certified0648swap : Certified (graph core0648) (root 7) 3 0 :=
  of_native_maps core0648 DegreeOneSmallSpectrum1463.graph DegreeOneSmallSpectrum945.graph
    sourceMap0648swap fusedMap0648swap sourceMap0648swap_checked fusedMap0648swap_checked
    DegreeOneSmallComparisons.comparison0648
#print axioms sourceMap0648swap_checked
#print axioms fusedMap0648swap_checked
#print axioms certified0648swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
