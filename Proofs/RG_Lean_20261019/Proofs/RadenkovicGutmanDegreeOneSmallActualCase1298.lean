/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1298 : Family 9 := level9.get ⟨64,by decide⟩
def sourceMap1298 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1298 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1298_checked : acceptsGraphIso
    (source (graph core1298) (root 9) 0 1) DegreeOneSmallSpectrum1268.graph sourceMap1298=true := by decide +kernel
theorem fusedMap1298_checked : acceptsGraphIso
    (fused (graph core1298) (root 9) 0 1) DegreeOneSmallSpectrum905.graph fusedMap1298=true := by decide +kernel
theorem certified1298 : Certified (graph core1298) (root 9) 0 1 :=
  of_native_maps core1298 DegreeOneSmallSpectrum1268.graph DegreeOneSmallSpectrum905.graph
    sourceMap1298 fusedMap1298 sourceMap1298_checked fusedMap1298_checked
    DegreeOneSmallComparisons.comparison1298
#print axioms sourceMap1298_checked
#print axioms fusedMap1298_checked
#print axioms certified1298
def sourceMap1298swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1298swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1298swap_checked : acceptsGraphIso
    (source (graph core1298) (root 9) 1 0) DegreeOneSmallSpectrum1268.graph sourceMap1298swap=true := by decide +kernel
theorem fusedMap1298swap_checked : acceptsGraphIso
    (fused (graph core1298) (root 9) 1 0) DegreeOneSmallSpectrum905.graph fusedMap1298swap=true := by decide +kernel
theorem certified1298swap : Certified (graph core1298) (root 9) 1 0 :=
  of_native_maps core1298 DegreeOneSmallSpectrum1268.graph DegreeOneSmallSpectrum905.graph
    sourceMap1298swap fusedMap1298swap sourceMap1298swap_checked fusedMap1298swap_checked
    DegreeOneSmallComparisons.comparison1298
#print axioms sourceMap1298swap_checked
#print axioms fusedMap1298swap_checked
#print axioms certified1298swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
