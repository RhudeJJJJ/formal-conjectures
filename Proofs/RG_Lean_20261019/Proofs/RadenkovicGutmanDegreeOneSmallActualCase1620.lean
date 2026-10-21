/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1620 : Family 9 := level9.get ⟨361,by decide⟩
def sourceMap1620 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1620 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1620_checked : acceptsGraphIso
    (source (graph core1620) (root 9) 0 1) DegreeOneSmallSpectrum1768.graph sourceMap1620=true := by decide +kernel
theorem fusedMap1620_checked : acceptsGraphIso
    (fused (graph core1620) (root 9) 0 1) DegreeOneSmallSpectrum1096.graph fusedMap1620=true := by decide +kernel
theorem certified1620 : Certified (graph core1620) (root 9) 0 1 :=
  of_native_maps core1620 DegreeOneSmallSpectrum1768.graph DegreeOneSmallSpectrum1096.graph
    sourceMap1620 fusedMap1620 sourceMap1620_checked fusedMap1620_checked
    DegreeOneSmallComparisons.comparison1620
#print axioms sourceMap1620_checked
#print axioms fusedMap1620_checked
#print axioms certified1620
def sourceMap1620swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1620swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1620swap_checked : acceptsGraphIso
    (source (graph core1620) (root 9) 1 0) DegreeOneSmallSpectrum1768.graph sourceMap1620swap=true := by decide +kernel
theorem fusedMap1620swap_checked : acceptsGraphIso
    (fused (graph core1620) (root 9) 1 0) DegreeOneSmallSpectrum1096.graph fusedMap1620swap=true := by decide +kernel
theorem certified1620swap : Certified (graph core1620) (root 9) 1 0 :=
  of_native_maps core1620 DegreeOneSmallSpectrum1768.graph DegreeOneSmallSpectrum1096.graph
    sourceMap1620swap fusedMap1620swap sourceMap1620swap_checked fusedMap1620swap_checked
    DegreeOneSmallComparisons.comparison1620
#print axioms sourceMap1620swap_checked
#print axioms fusedMap1620swap_checked
#print axioms certified1620swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
