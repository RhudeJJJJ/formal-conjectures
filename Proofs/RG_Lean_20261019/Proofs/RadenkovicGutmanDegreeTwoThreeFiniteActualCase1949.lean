/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1949 : Family 10 := level10.get ⟨1481,by decide⟩
def sourceMap1949 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1949 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1949_checked : acceptsGraphIso
    (source (graph core1949) (root 10) 0 2) DegreeTwoThreeSpectrum3490.graph sourceMap1949=true := by decide +kernel
theorem fusedMap1949_checked : acceptsGraphIso
    (fused (graph core1949) (root 10) 0 2) DegreeTwoThreeSpectrum3721.graph fusedMap1949=true := by decide +kernel
theorem certified1949 : Certified (graph core1949) (root 10) 0 2 :=
  of_native_maps core1949 DegreeTwoThreeSpectrum3490.graph DegreeTwoThreeSpectrum3721.graph
    sourceMap1949 fusedMap1949 sourceMap1949_checked fusedMap1949_checked
    DegreeTwoThreeFiniteComparisons.comparison1949
#print axioms sourceMap1949_checked
#print axioms fusedMap1949_checked
#print axioms certified1949
def sourceMap1949swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1949swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1949swap_checked : acceptsGraphIso
    (source (graph core1949) (root 10) 2 0) DegreeTwoThreeSpectrum3490.graph sourceMap1949swap=true := by decide +kernel
theorem fusedMap1949swap_checked : acceptsGraphIso
    (fused (graph core1949) (root 10) 2 0) DegreeTwoThreeSpectrum3721.graph fusedMap1949swap=true := by decide +kernel
theorem certified1949swap : Certified (graph core1949) (root 10) 2 0 :=
  of_native_maps core1949 DegreeTwoThreeSpectrum3490.graph DegreeTwoThreeSpectrum3721.graph
    sourceMap1949swap fusedMap1949swap sourceMap1949swap_checked fusedMap1949swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1949
#print axioms sourceMap1949swap_checked
#print axioms fusedMap1949swap_checked
#print axioms certified1949swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
