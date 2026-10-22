/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1153 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap1153 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,4,5,6,7,1,2,3] (sourceLabel 8 0 2 v)
def fusedMap1153 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 0 2 v)
theorem sourceMap1153_checked : acceptsGraphIso
    (source (graph core1153) (root 8) 0 2) DegreeOneSmallSpectrum1470.graph sourceMap1153=true := by decide +kernel
theorem fusedMap1153_checked : acceptsGraphIso
    (fused (graph core1153) (root 8) 0 2) DegreeOneSmallSpectrum1505.graph fusedMap1153=true := by decide +kernel
theorem certified1153 : Certified (graph core1153) (root 8) 0 2 :=
  of_native_maps core1153 DegreeOneSmallSpectrum1470.graph DegreeOneSmallSpectrum1505.graph
    sourceMap1153 fusedMap1153 sourceMap1153_checked fusedMap1153_checked
    DegreeTwoThreeFiniteComparisons.comparison1153
#print axioms sourceMap1153_checked
#print axioms fusedMap1153_checked
#print axioms certified1153
def sourceMap1153swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,4,5,6,1,2,3,7] (sourceLabel 8 2 0 v)
def fusedMap1153swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 2 0 v)
theorem sourceMap1153swap_checked : acceptsGraphIso
    (source (graph core1153) (root 8) 2 0) DegreeOneSmallSpectrum1470.graph sourceMap1153swap=true := by decide +kernel
theorem fusedMap1153swap_checked : acceptsGraphIso
    (fused (graph core1153) (root 8) 2 0) DegreeOneSmallSpectrum1505.graph fusedMap1153swap=true := by decide +kernel
theorem certified1153swap : Certified (graph core1153) (root 8) 2 0 :=
  of_native_maps core1153 DegreeOneSmallSpectrum1470.graph DegreeOneSmallSpectrum1505.graph
    sourceMap1153swap fusedMap1153swap sourceMap1153swap_checked fusedMap1153swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1153
#print axioms sourceMap1153swap_checked
#print axioms fusedMap1153swap_checked
#print axioms certified1153swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
