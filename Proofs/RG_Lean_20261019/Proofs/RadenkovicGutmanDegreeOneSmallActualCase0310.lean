/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0310 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0310 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,5,6,1,2,3,4] (sourceLabel 6 1 3 v)
def fusedMap0310 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0310_checked : acceptsGraphIso
    (source (graph core0310) (root 6) 1 3) DegreeOneSmallSpectrum970.graph sourceMap0310=true := by decide +kernel
theorem fusedMap0310_checked : acceptsGraphIso
    (fused (graph core0310) (root 6) 1 3) DegreeOneSmallSpectrum859.graph fusedMap0310=true := by decide +kernel
theorem certified0310 : Certified (graph core0310) (root 6) 1 3 :=
  of_native_maps core0310 DegreeOneSmallSpectrum970.graph DegreeOneSmallSpectrum859.graph
    sourceMap0310 fusedMap0310 sourceMap0310_checked fusedMap0310_checked
    DegreeOneSmallComparisons.comparison0310
#print axioms sourceMap0310_checked
#print axioms fusedMap0310_checked
#print axioms certified0310
def sourceMap0310swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 3 1 v)
def fusedMap0310swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0310swap_checked : acceptsGraphIso
    (source (graph core0310) (root 6) 3 1) DegreeOneSmallSpectrum970.graph sourceMap0310swap=true := by decide +kernel
theorem fusedMap0310swap_checked : acceptsGraphIso
    (fused (graph core0310) (root 6) 3 1) DegreeOneSmallSpectrum859.graph fusedMap0310swap=true := by decide +kernel
theorem certified0310swap : Certified (graph core0310) (root 6) 3 1 :=
  of_native_maps core0310 DegreeOneSmallSpectrum970.graph DegreeOneSmallSpectrum859.graph
    sourceMap0310swap fusedMap0310swap sourceMap0310swap_checked fusedMap0310swap_checked
    DegreeOneSmallComparisons.comparison0310
#print axioms sourceMap0310swap_checked
#print axioms fusedMap0310swap_checked
#print axioms certified0310swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
