/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0647 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0647 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0647 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0647_checked : acceptsGraphIso
    (source (graph core0647) (root 7) 0 2) DegreeOneSmallSpectrum562.graph sourceMap0647=true := by decide +kernel
theorem fusedMap0647_checked : acceptsGraphIso
    (fused (graph core0647) (root 7) 0 2) DegreeOneSmallSpectrum563.graph fusedMap0647=true := by decide +kernel
theorem certified0647 : Certified (graph core0647) (root 7) 0 2 :=
  of_native_maps core0647 DegreeOneSmallSpectrum562.graph DegreeOneSmallSpectrum563.graph
    sourceMap0647 fusedMap0647 sourceMap0647_checked fusedMap0647_checked
    DegreeOneSmallComparisons.comparison0647
#print axioms sourceMap0647_checked
#print axioms fusedMap0647_checked
#print axioms certified0647
def sourceMap0647swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0647swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0647swap_checked : acceptsGraphIso
    (source (graph core0647) (root 7) 2 0) DegreeOneSmallSpectrum562.graph sourceMap0647swap=true := by decide +kernel
theorem fusedMap0647swap_checked : acceptsGraphIso
    (fused (graph core0647) (root 7) 2 0) DegreeOneSmallSpectrum563.graph fusedMap0647swap=true := by decide +kernel
theorem certified0647swap : Certified (graph core0647) (root 7) 2 0 :=
  of_native_maps core0647 DegreeOneSmallSpectrum562.graph DegreeOneSmallSpectrum563.graph
    sourceMap0647swap fusedMap0647swap sourceMap0647swap_checked fusedMap0647swap_checked
    DegreeOneSmallComparisons.comparison0647
#print axioms sourceMap0647swap_checked
#print axioms fusedMap0647swap_checked
#print axioms certified0647swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
