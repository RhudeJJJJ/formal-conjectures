/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1288 : Family 9 := level9.get ⟨57,by decide⟩
def sourceMap1288 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1288 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1288_checked : acceptsGraphIso
    (source (graph core1288) (root 9) 0 1) DegreeOneSmallSpectrum1238.graph sourceMap1288=true := by decide +kernel
theorem fusedMap1288_checked : acceptsGraphIso
    (fused (graph core1288) (root 9) 0 1) DegreeOneSmallSpectrum882.graph fusedMap1288=true := by decide +kernel
theorem certified1288 : Certified (graph core1288) (root 9) 0 1 :=
  of_native_maps core1288 DegreeOneSmallSpectrum1238.graph DegreeOneSmallSpectrum882.graph
    sourceMap1288 fusedMap1288 sourceMap1288_checked fusedMap1288_checked
    DegreeOneSmallComparisons.comparison1288
#print axioms sourceMap1288_checked
#print axioms fusedMap1288_checked
#print axioms certified1288
def sourceMap1288swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1288swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1288swap_checked : acceptsGraphIso
    (source (graph core1288) (root 9) 1 0) DegreeOneSmallSpectrum1238.graph sourceMap1288swap=true := by decide +kernel
theorem fusedMap1288swap_checked : acceptsGraphIso
    (fused (graph core1288) (root 9) 1 0) DegreeOneSmallSpectrum882.graph fusedMap1288swap=true := by decide +kernel
theorem certified1288swap : Certified (graph core1288) (root 9) 1 0 :=
  of_native_maps core1288 DegreeOneSmallSpectrum1238.graph DegreeOneSmallSpectrum882.graph
    sourceMap1288swap fusedMap1288swap sourceMap1288swap_checked fusedMap1288swap_checked
    DegreeOneSmallComparisons.comparison1288
#print axioms sourceMap1288swap_checked
#print axioms fusedMap1288swap_checked
#print axioms certified1288swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
