/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1280 : Family 9 := level9.get ⟨52,by decide⟩
def sourceMap1280 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1280 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1280_checked : acceptsGraphIso
    (source (graph core1280) (root 9) 0 1) DegreeOneSmallSpectrum1173.graph sourceMap1280=true := by decide +kernel
theorem fusedMap1280_checked : acceptsGraphIso
    (fused (graph core1280) (root 9) 0 1) DegreeOneSmallSpectrum874.graph fusedMap1280=true := by decide +kernel
theorem certified1280 : Certified (graph core1280) (root 9) 0 1 :=
  of_native_maps core1280 DegreeOneSmallSpectrum1173.graph DegreeOneSmallSpectrum874.graph
    sourceMap1280 fusedMap1280 sourceMap1280_checked fusedMap1280_checked
    DegreeOneSmallComparisons.comparison1280
#print axioms sourceMap1280_checked
#print axioms fusedMap1280_checked
#print axioms certified1280
def sourceMap1280swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1280swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1280swap_checked : acceptsGraphIso
    (source (graph core1280) (root 9) 1 0) DegreeOneSmallSpectrum1173.graph sourceMap1280swap=true := by decide +kernel
theorem fusedMap1280swap_checked : acceptsGraphIso
    (fused (graph core1280) (root 9) 1 0) DegreeOneSmallSpectrum874.graph fusedMap1280swap=true := by decide +kernel
theorem certified1280swap : Certified (graph core1280) (root 9) 1 0 :=
  of_native_maps core1280 DegreeOneSmallSpectrum1173.graph DegreeOneSmallSpectrum874.graph
    sourceMap1280swap fusedMap1280swap sourceMap1280swap_checked fusedMap1280swap_checked
    DegreeOneSmallComparisons.comparison1280
#print axioms sourceMap1280swap_checked
#print axioms fusedMap1280swap_checked
#print axioms certified1280swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
