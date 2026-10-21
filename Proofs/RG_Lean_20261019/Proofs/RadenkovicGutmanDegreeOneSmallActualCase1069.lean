/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1069 : Family 8 := level8.get ⟨134,by decide⟩
def sourceMap1069 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1069 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1069_checked : acceptsGraphIso
    (source (graph core1069) (root 8) 0 2) DegreeOneSmallSpectrum1305.graph sourceMap1069=true := by decide +kernel
theorem fusedMap1069_checked : acceptsGraphIso
    (fused (graph core1069) (root 8) 0 2) DegreeOneSmallSpectrum1306.graph fusedMap1069=true := by decide +kernel
theorem certified1069 : Certified (graph core1069) (root 8) 0 2 :=
  of_native_maps core1069 DegreeOneSmallSpectrum1305.graph DegreeOneSmallSpectrum1306.graph
    sourceMap1069 fusedMap1069 sourceMap1069_checked fusedMap1069_checked
    DegreeOneSmallComparisons.comparison1069
#print axioms sourceMap1069_checked
#print axioms fusedMap1069_checked
#print axioms certified1069
def sourceMap1069swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1069swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1069swap_checked : acceptsGraphIso
    (source (graph core1069) (root 8) 2 0) DegreeOneSmallSpectrum1305.graph sourceMap1069swap=true := by decide +kernel
theorem fusedMap1069swap_checked : acceptsGraphIso
    (fused (graph core1069) (root 8) 2 0) DegreeOneSmallSpectrum1306.graph fusedMap1069swap=true := by decide +kernel
theorem certified1069swap : Certified (graph core1069) (root 8) 2 0 :=
  of_native_maps core1069 DegreeOneSmallSpectrum1305.graph DegreeOneSmallSpectrum1306.graph
    sourceMap1069swap fusedMap1069swap sourceMap1069swap_checked fusedMap1069swap_checked
    DegreeOneSmallComparisons.comparison1069
#print axioms sourceMap1069swap_checked
#print axioms fusedMap1069swap_checked
#print axioms certified1069swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
