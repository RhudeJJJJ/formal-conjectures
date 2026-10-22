/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1235 : Family 9 := level9.get ⟨172,by decide⟩
def sourceMap1235 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1235 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1235_checked : acceptsGraphIso
    (source (graph core1235) (root 9) 0 2) DegreeTwoThreeSpectrum2033.graph sourceMap1235=true := by decide +kernel
theorem fusedMap1235_checked : acceptsGraphIso
    (fused (graph core1235) (root 9) 0 2) DegreeTwoThreeSpectrum1773.graph fusedMap1235=true := by decide +kernel
theorem certified1235 : Certified (graph core1235) (root 9) 0 2 :=
  of_native_maps core1235 DegreeTwoThreeSpectrum2033.graph DegreeTwoThreeSpectrum1773.graph
    sourceMap1235 fusedMap1235 sourceMap1235_checked fusedMap1235_checked
    DegreeTwoThreeFiniteComparisons.comparison1235
#print axioms sourceMap1235_checked
#print axioms fusedMap1235_checked
#print axioms certified1235
def sourceMap1235swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1235swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1235swap_checked : acceptsGraphIso
    (source (graph core1235) (root 9) 2 0) DegreeTwoThreeSpectrum2033.graph sourceMap1235swap=true := by decide +kernel
theorem fusedMap1235swap_checked : acceptsGraphIso
    (fused (graph core1235) (root 9) 2 0) DegreeTwoThreeSpectrum1773.graph fusedMap1235swap=true := by decide +kernel
theorem certified1235swap : Certified (graph core1235) (root 9) 2 0 :=
  of_native_maps core1235 DegreeTwoThreeSpectrum2033.graph DegreeTwoThreeSpectrum1773.graph
    sourceMap1235swap fusedMap1235swap sourceMap1235swap_checked fusedMap1235swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1235
#print axioms sourceMap1235swap_checked
#print axioms fusedMap1235swap_checked
#print axioms certified1235swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
