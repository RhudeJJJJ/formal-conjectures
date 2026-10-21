/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1434 : Family 9 := level9.get ⟨170,by decide⟩
def sourceMap1434 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1434 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1434_checked : acceptsGraphIso
    (source (graph core1434) (root 9) 0 1) DegreeOneSmallSpectrum1171.graph sourceMap1434=true := by decide +kernel
theorem fusedMap1434_checked : acceptsGraphIso
    (fused (graph core1434) (root 9) 0 1) DegreeOneSmallSpectrum1182.graph fusedMap1434=true := by decide +kernel
theorem certified1434 : Certified (graph core1434) (root 9) 0 1 :=
  of_native_maps core1434 DegreeOneSmallSpectrum1171.graph DegreeOneSmallSpectrum1182.graph
    sourceMap1434 fusedMap1434 sourceMap1434_checked fusedMap1434_checked
    DegreeOneSmallComparisons.comparison1434
#print axioms sourceMap1434_checked
#print axioms fusedMap1434_checked
#print axioms certified1434
def sourceMap1434swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1434swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1434swap_checked : acceptsGraphIso
    (source (graph core1434) (root 9) 1 0) DegreeOneSmallSpectrum1171.graph sourceMap1434swap=true := by decide +kernel
theorem fusedMap1434swap_checked : acceptsGraphIso
    (fused (graph core1434) (root 9) 1 0) DegreeOneSmallSpectrum1182.graph fusedMap1434swap=true := by decide +kernel
theorem certified1434swap : Certified (graph core1434) (root 9) 1 0 :=
  of_native_maps core1434 DegreeOneSmallSpectrum1171.graph DegreeOneSmallSpectrum1182.graph
    sourceMap1434swap fusedMap1434swap sourceMap1434swap_checked fusedMap1434swap_checked
    DegreeOneSmallComparisons.comparison1434
#print axioms sourceMap1434swap_checked
#print axioms fusedMap1434swap_checked
#print axioms certified1434swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
