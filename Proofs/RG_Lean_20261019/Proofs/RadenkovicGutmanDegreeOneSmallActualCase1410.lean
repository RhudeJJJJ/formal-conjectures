/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1410 : Family 9 := level9.get ⟨152,by decide⟩
def sourceMap1410 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1410 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1410_checked : acceptsGraphIso
    (source (graph core1410) (root 9) 0 1) DegreeOneSmallSpectrum1071.graph sourceMap1410=true := by decide +kernel
theorem fusedMap1410_checked : acceptsGraphIso
    (fused (graph core1410) (root 9) 0 1) DegreeOneSmallSpectrum1082.graph fusedMap1410=true := by decide +kernel
theorem certified1410 : Certified (graph core1410) (root 9) 0 1 :=
  of_native_maps core1410 DegreeOneSmallSpectrum1071.graph DegreeOneSmallSpectrum1082.graph
    sourceMap1410 fusedMap1410 sourceMap1410_checked fusedMap1410_checked
    DegreeOneSmallComparisons.comparison1410
#print axioms sourceMap1410_checked
#print axioms fusedMap1410_checked
#print axioms certified1410
def sourceMap1410swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1410swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1410swap_checked : acceptsGraphIso
    (source (graph core1410) (root 9) 1 0) DegreeOneSmallSpectrum1071.graph sourceMap1410swap=true := by decide +kernel
theorem fusedMap1410swap_checked : acceptsGraphIso
    (fused (graph core1410) (root 9) 1 0) DegreeOneSmallSpectrum1082.graph fusedMap1410swap=true := by decide +kernel
theorem certified1410swap : Certified (graph core1410) (root 9) 1 0 :=
  of_native_maps core1410 DegreeOneSmallSpectrum1071.graph DegreeOneSmallSpectrum1082.graph
    sourceMap1410swap fusedMap1410swap sourceMap1410swap_checked fusedMap1410swap_checked
    DegreeOneSmallComparisons.comparison1410
#print axioms sourceMap1410swap_checked
#print axioms fusedMap1410swap_checked
#print axioms certified1410swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
