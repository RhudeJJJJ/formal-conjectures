/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1915 : Family 10 := level10.get ⟨1410,by decide⟩
def sourceMap1915 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1915 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1915_checked : acceptsGraphIso
    (source (graph core1915) (root 10) 0 2) DegreeTwoThreeSpectrum3619.graph sourceMap1915=true := by decide +kernel
theorem fusedMap1915_checked : acceptsGraphIso
    (fused (graph core1915) (root 10) 0 2) DegreeTwoThreeSpectrum3620.graph fusedMap1915=true := by decide +kernel
theorem certified1915 : Certified (graph core1915) (root 10) 0 2 :=
  of_native_maps core1915 DegreeTwoThreeSpectrum3619.graph DegreeTwoThreeSpectrum3620.graph
    sourceMap1915 fusedMap1915 sourceMap1915_checked fusedMap1915_checked
    DegreeTwoThreeFiniteComparisons.comparison1915
#print axioms sourceMap1915_checked
#print axioms fusedMap1915_checked
#print axioms certified1915
def sourceMap1915swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1915swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1915swap_checked : acceptsGraphIso
    (source (graph core1915) (root 10) 2 0) DegreeTwoThreeSpectrum3619.graph sourceMap1915swap=true := by decide +kernel
theorem fusedMap1915swap_checked : acceptsGraphIso
    (fused (graph core1915) (root 10) 2 0) DegreeTwoThreeSpectrum3620.graph fusedMap1915swap=true := by decide +kernel
theorem certified1915swap : Certified (graph core1915) (root 10) 2 0 :=
  of_native_maps core1915 DegreeTwoThreeSpectrum3619.graph DegreeTwoThreeSpectrum3620.graph
    sourceMap1915swap fusedMap1915swap sourceMap1915swap_checked fusedMap1915swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1915
#print axioms sourceMap1915swap_checked
#print axioms fusedMap1915swap_checked
#print axioms certified1915swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
