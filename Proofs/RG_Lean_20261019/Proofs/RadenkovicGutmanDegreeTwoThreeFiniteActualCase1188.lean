/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1188 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap1188 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 0 2 v)
def fusedMap1188 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1188_checked : acceptsGraphIso
    (source (graph core1188) (root 8) 0 2) DegreeOneSmallSpectrum1523.graph sourceMap1188=true := by decide +kernel
theorem fusedMap1188_checked : acceptsGraphIso
    (fused (graph core1188) (root 8) 0 2) DegreeOneSmallSpectrum1526.graph fusedMap1188=true := by decide +kernel
theorem certified1188 : Certified (graph core1188) (root 8) 0 2 :=
  of_native_maps core1188 DegreeOneSmallSpectrum1523.graph DegreeOneSmallSpectrum1526.graph
    sourceMap1188 fusedMap1188 sourceMap1188_checked fusedMap1188_checked
    DegreeTwoThreeFiniteComparisons.comparison1188
#print axioms sourceMap1188_checked
#print axioms fusedMap1188_checked
#print axioms certified1188
def sourceMap1188swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,9] (sourceLabel 8 2 0 v)
def fusedMap1188swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1188swap_checked : acceptsGraphIso
    (source (graph core1188) (root 8) 2 0) DegreeOneSmallSpectrum1523.graph sourceMap1188swap=true := by decide +kernel
theorem fusedMap1188swap_checked : acceptsGraphIso
    (fused (graph core1188) (root 8) 2 0) DegreeOneSmallSpectrum1526.graph fusedMap1188swap=true := by decide +kernel
theorem certified1188swap : Certified (graph core1188) (root 8) 2 0 :=
  of_native_maps core1188 DegreeOneSmallSpectrum1523.graph DegreeOneSmallSpectrum1526.graph
    sourceMap1188swap fusedMap1188swap sourceMap1188swap_checked fusedMap1188swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1188
#print axioms sourceMap1188swap_checked
#print axioms fusedMap1188swap_checked
#print axioms certified1188swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
