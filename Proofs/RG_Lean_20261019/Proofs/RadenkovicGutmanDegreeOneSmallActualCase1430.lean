/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1430 : Family 9 := level9.get ⟨167,by decide⟩
def sourceMap1430 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1430 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1430_checked : acceptsGraphIso
    (source (graph core1430) (root 9) 0 1) DegreeOneSmallSpectrum1153.graph sourceMap1430=true := by decide +kernel
theorem fusedMap1430_checked : acceptsGraphIso
    (fused (graph core1430) (root 9) 0 1) DegreeOneSmallSpectrum1158.graph fusedMap1430=true := by decide +kernel
theorem certified1430 : Certified (graph core1430) (root 9) 0 1 :=
  of_native_maps core1430 DegreeOneSmallSpectrum1153.graph DegreeOneSmallSpectrum1158.graph
    sourceMap1430 fusedMap1430 sourceMap1430_checked fusedMap1430_checked
    DegreeOneSmallComparisons.comparison1430
#print axioms sourceMap1430_checked
#print axioms fusedMap1430_checked
#print axioms certified1430
def sourceMap1430swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1430swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1430swap_checked : acceptsGraphIso
    (source (graph core1430) (root 9) 1 0) DegreeOneSmallSpectrum1153.graph sourceMap1430swap=true := by decide +kernel
theorem fusedMap1430swap_checked : acceptsGraphIso
    (fused (graph core1430) (root 9) 1 0) DegreeOneSmallSpectrum1158.graph fusedMap1430swap=true := by decide +kernel
theorem certified1430swap : Certified (graph core1430) (root 9) 1 0 :=
  of_native_maps core1430 DegreeOneSmallSpectrum1153.graph DegreeOneSmallSpectrum1158.graph
    sourceMap1430swap fusedMap1430swap sourceMap1430swap_checked fusedMap1430swap_checked
    DegreeOneSmallComparisons.comparison1430
#print axioms sourceMap1430swap_checked
#print axioms fusedMap1430swap_checked
#print axioms certified1430swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
