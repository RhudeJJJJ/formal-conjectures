/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1466 : Family 9 := level9.get ⟨202,by decide⟩
def sourceMap1466 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1466 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1466_checked : acceptsGraphIso
    (source (graph core1466) (root 9) 0 1) DegreeOneSmallSpectrum1308.graph sourceMap1466=true := by decide +kernel
theorem fusedMap1466_checked : acceptsGraphIso
    (fused (graph core1466) (root 9) 0 1) DegreeOneSmallSpectrum1313.graph fusedMap1466=true := by decide +kernel
theorem certified1466 : Certified (graph core1466) (root 9) 0 1 :=
  of_native_maps core1466 DegreeOneSmallSpectrum1308.graph DegreeOneSmallSpectrum1313.graph
    sourceMap1466 fusedMap1466 sourceMap1466_checked fusedMap1466_checked
    DegreeOneSmallComparisons.comparison1466
#print axioms sourceMap1466_checked
#print axioms fusedMap1466_checked
#print axioms certified1466
def sourceMap1466swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1466swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1466swap_checked : acceptsGraphIso
    (source (graph core1466) (root 9) 1 0) DegreeOneSmallSpectrum1308.graph sourceMap1466swap=true := by decide +kernel
theorem fusedMap1466swap_checked : acceptsGraphIso
    (fused (graph core1466) (root 9) 1 0) DegreeOneSmallSpectrum1313.graph fusedMap1466swap=true := by decide +kernel
theorem certified1466swap : Certified (graph core1466) (root 9) 1 0 :=
  of_native_maps core1466 DegreeOneSmallSpectrum1308.graph DegreeOneSmallSpectrum1313.graph
    sourceMap1466swap fusedMap1466swap sourceMap1466swap_checked fusedMap1466swap_checked
    DegreeOneSmallComparisons.comparison1466
#print axioms sourceMap1466swap_checked
#print axioms fusedMap1466swap_checked
#print axioms certified1466swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
