/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1272 : Family 9 := level9.get ⟨47,by decide⟩
def sourceMap1272 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1272 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1272_checked : acceptsGraphIso
    (source (graph core1272) (root 9) 0 1) DegreeOneSmallSpectrum1072.graph sourceMap1272=true := by decide +kernel
theorem fusedMap1272_checked : acceptsGraphIso
    (fused (graph core1272) (root 9) 0 1) DegreeOneSmallSpectrum869.graph fusedMap1272=true := by decide +kernel
theorem certified1272 : Certified (graph core1272) (root 9) 0 1 :=
  of_native_maps core1272 DegreeOneSmallSpectrum1072.graph DegreeOneSmallSpectrum869.graph
    sourceMap1272 fusedMap1272 sourceMap1272_checked fusedMap1272_checked
    DegreeOneSmallComparisons.comparison1272
#print axioms sourceMap1272_checked
#print axioms fusedMap1272_checked
#print axioms certified1272
def sourceMap1272swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1272swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1272swap_checked : acceptsGraphIso
    (source (graph core1272) (root 9) 1 0) DegreeOneSmallSpectrum1072.graph sourceMap1272swap=true := by decide +kernel
theorem fusedMap1272swap_checked : acceptsGraphIso
    (fused (graph core1272) (root 9) 1 0) DegreeOneSmallSpectrum869.graph fusedMap1272swap=true := by decide +kernel
theorem certified1272swap : Certified (graph core1272) (root 9) 1 0 :=
  of_native_maps core1272 DegreeOneSmallSpectrum1072.graph DegreeOneSmallSpectrum869.graph
    sourceMap1272swap fusedMap1272swap sourceMap1272swap_checked fusedMap1272swap_checked
    DegreeOneSmallComparisons.comparison1272
#print axioms sourceMap1272swap_checked
#print axioms fusedMap1272swap_checked
#print axioms certified1272swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
