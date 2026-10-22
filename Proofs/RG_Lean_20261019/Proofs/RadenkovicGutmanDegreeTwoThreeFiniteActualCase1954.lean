/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1954 : Family 10 := level10.get ⟨1498,by decide⟩
def sourceMap1954 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1954 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1954_checked : acceptsGraphIso
    (source (graph core1954) (root 10) 0 2) DegreeTwoThreeSpectrum3219.graph sourceMap1954=true := by decide +kernel
theorem fusedMap1954_checked : acceptsGraphIso
    (fused (graph core1954) (root 10) 0 2) DegreeTwoThreeSpectrum3726.graph fusedMap1954=true := by decide +kernel
theorem certified1954 : Certified (graph core1954) (root 10) 0 2 :=
  of_native_maps core1954 DegreeTwoThreeSpectrum3219.graph DegreeTwoThreeSpectrum3726.graph
    sourceMap1954 fusedMap1954 sourceMap1954_checked fusedMap1954_checked
    DegreeTwoThreeFiniteComparisons.comparison1954
#print axioms sourceMap1954_checked
#print axioms fusedMap1954_checked
#print axioms certified1954
def sourceMap1954swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1954swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1954swap_checked : acceptsGraphIso
    (source (graph core1954) (root 10) 2 0) DegreeTwoThreeSpectrum3219.graph sourceMap1954swap=true := by decide +kernel
theorem fusedMap1954swap_checked : acceptsGraphIso
    (fused (graph core1954) (root 10) 2 0) DegreeTwoThreeSpectrum3726.graph fusedMap1954swap=true := by decide +kernel
theorem certified1954swap : Certified (graph core1954) (root 10) 2 0 :=
  of_native_maps core1954 DegreeTwoThreeSpectrum3219.graph DegreeTwoThreeSpectrum3726.graph
    sourceMap1954swap fusedMap1954swap sourceMap1954swap_checked fusedMap1954swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1954
#print axioms sourceMap1954swap_checked
#print axioms fusedMap1954swap_checked
#print axioms certified1954swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
