/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1206 : Family 9 := level9.get ⟨73,by decide⟩
def sourceMap1206 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1206 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1206_checked : acceptsGraphIso
    (source (graph core1206) (root 9) 0 2) DegreeTwoThreeSpectrum1815.graph sourceMap1206=true := by decide +kernel
theorem fusedMap1206_checked : acceptsGraphIso
    (fused (graph core1206) (root 9) 0 2) DegreeTwoThreeSpectrum1817.graph fusedMap1206=true := by decide +kernel
theorem certified1206 : Certified (graph core1206) (root 9) 0 2 :=
  of_native_maps core1206 DegreeTwoThreeSpectrum1815.graph DegreeTwoThreeSpectrum1817.graph
    sourceMap1206 fusedMap1206 sourceMap1206_checked fusedMap1206_checked
    DegreeTwoThreeFiniteComparisons.comparison1206
#print axioms sourceMap1206_checked
#print axioms fusedMap1206_checked
#print axioms certified1206
def sourceMap1206swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1206swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1206swap_checked : acceptsGraphIso
    (source (graph core1206) (root 9) 2 0) DegreeTwoThreeSpectrum1815.graph sourceMap1206swap=true := by decide +kernel
theorem fusedMap1206swap_checked : acceptsGraphIso
    (fused (graph core1206) (root 9) 2 0) DegreeTwoThreeSpectrum1817.graph fusedMap1206swap=true := by decide +kernel
theorem certified1206swap : Certified (graph core1206) (root 9) 2 0 :=
  of_native_maps core1206 DegreeTwoThreeSpectrum1815.graph DegreeTwoThreeSpectrum1817.graph
    sourceMap1206swap fusedMap1206swap sourceMap1206swap_checked fusedMap1206swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1206
#print axioms sourceMap1206swap_checked
#print axioms fusedMap1206swap_checked
#print axioms certified1206swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
