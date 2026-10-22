/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1193 : Family 9 := level9.get ⟨15,by decide⟩
def sourceMap1193 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1193 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1193_checked : acceptsGraphIso
    (source (graph core1193) (root 9) 0 2) DegreeTwoThreeSpectrum1798.graph sourceMap1193=true := by decide +kernel
theorem fusedMap1193_checked : acceptsGraphIso
    (fused (graph core1193) (root 9) 0 2) DegreeTwoThreeSpectrum1714.graph fusedMap1193=true := by decide +kernel
theorem certified1193 : Certified (graph core1193) (root 9) 0 2 :=
  of_native_maps core1193 DegreeTwoThreeSpectrum1798.graph DegreeTwoThreeSpectrum1714.graph
    sourceMap1193 fusedMap1193 sourceMap1193_checked fusedMap1193_checked
    DegreeTwoThreeFiniteComparisons.comparison1193
#print axioms sourceMap1193_checked
#print axioms fusedMap1193_checked
#print axioms certified1193
def sourceMap1193swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1193swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1193swap_checked : acceptsGraphIso
    (source (graph core1193) (root 9) 2 0) DegreeTwoThreeSpectrum1798.graph sourceMap1193swap=true := by decide +kernel
theorem fusedMap1193swap_checked : acceptsGraphIso
    (fused (graph core1193) (root 9) 2 0) DegreeTwoThreeSpectrum1714.graph fusedMap1193swap=true := by decide +kernel
theorem certified1193swap : Certified (graph core1193) (root 9) 2 0 :=
  of_native_maps core1193 DegreeTwoThreeSpectrum1798.graph DegreeTwoThreeSpectrum1714.graph
    sourceMap1193swap fusedMap1193swap sourceMap1193swap_checked fusedMap1193swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1193
#print axioms sourceMap1193swap_checked
#print axioms fusedMap1193swap_checked
#print axioms certified1193swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
