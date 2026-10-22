/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1186 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap1186 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,5,6,7] (sourceLabel 8 0 2 v)
def fusedMap1186 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1186_checked : acceptsGraphIso
    (source (graph core1186) (root 8) 0 2) DegreeOneSmallSpectrum1966.graph sourceMap1186=true := by decide +kernel
theorem fusedMap1186_checked : acceptsGraphIso
    (fused (graph core1186) (root 8) 0 2) DegreeOneSmallSpectrum1399.graph fusedMap1186=true := by decide +kernel
theorem certified1186 : Certified (graph core1186) (root 8) 0 2 :=
  of_native_maps core1186 DegreeOneSmallSpectrum1966.graph DegreeOneSmallSpectrum1399.graph
    sourceMap1186 fusedMap1186 sourceMap1186_checked fusedMap1186_checked
    DegreeTwoThreeFiniteComparisons.comparison1186
#print axioms sourceMap1186_checked
#print axioms fusedMap1186_checked
#print axioms certified1186
def sourceMap1186swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7,12] (sourceLabel 8 2 0 v)
def fusedMap1186swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1186swap_checked : acceptsGraphIso
    (source (graph core1186) (root 8) 2 0) DegreeOneSmallSpectrum1966.graph sourceMap1186swap=true := by decide +kernel
theorem fusedMap1186swap_checked : acceptsGraphIso
    (fused (graph core1186) (root 8) 2 0) DegreeOneSmallSpectrum1399.graph fusedMap1186swap=true := by decide +kernel
theorem certified1186swap : Certified (graph core1186) (root 8) 2 0 :=
  of_native_maps core1186 DegreeOneSmallSpectrum1966.graph DegreeOneSmallSpectrum1399.graph
    sourceMap1186swap fusedMap1186swap sourceMap1186swap_checked fusedMap1186swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1186
#print axioms sourceMap1186swap_checked
#print axioms fusedMap1186swap_checked
#print axioms certified1186swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
