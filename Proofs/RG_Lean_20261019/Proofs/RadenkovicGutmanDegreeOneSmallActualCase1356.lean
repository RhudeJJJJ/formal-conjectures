/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1356 : Family 9 := level9.get ⟨105,by decide⟩
def sourceMap1356 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1356 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1356_checked : acceptsGraphIso
    (source (graph core1356) (root 9) 0 1) DegreeOneSmallSpectrum1433.graph sourceMap1356=true := by decide +kernel
theorem fusedMap1356_checked : acceptsGraphIso
    (fused (graph core1356) (root 9) 0 1) DegreeOneSmallSpectrum960.graph fusedMap1356=true := by decide +kernel
theorem certified1356 : Certified (graph core1356) (root 9) 0 1 :=
  of_native_maps core1356 DegreeOneSmallSpectrum1433.graph DegreeOneSmallSpectrum960.graph
    sourceMap1356 fusedMap1356 sourceMap1356_checked fusedMap1356_checked
    DegreeOneSmallComparisons.comparison1356
#print axioms sourceMap1356_checked
#print axioms fusedMap1356_checked
#print axioms certified1356
def sourceMap1356swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1356swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1356swap_checked : acceptsGraphIso
    (source (graph core1356) (root 9) 1 0) DegreeOneSmallSpectrum1433.graph sourceMap1356swap=true := by decide +kernel
theorem fusedMap1356swap_checked : acceptsGraphIso
    (fused (graph core1356) (root 9) 1 0) DegreeOneSmallSpectrum960.graph fusedMap1356swap=true := by decide +kernel
theorem certified1356swap : Certified (graph core1356) (root 9) 1 0 :=
  of_native_maps core1356 DegreeOneSmallSpectrum1433.graph DegreeOneSmallSpectrum960.graph
    sourceMap1356swap fusedMap1356swap sourceMap1356swap_checked fusedMap1356swap_checked
    DegreeOneSmallComparisons.comparison1356
#print axioms sourceMap1356swap_checked
#print axioms fusedMap1356swap_checked
#print axioms certified1356swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
