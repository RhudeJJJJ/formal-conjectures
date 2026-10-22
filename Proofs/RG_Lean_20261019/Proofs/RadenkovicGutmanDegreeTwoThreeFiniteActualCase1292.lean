/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1292 : Family 9 := level9.get ⟨336,by decide⟩
def sourceMap1292 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1292 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1292_checked : acceptsGraphIso
    (source (graph core1292) (root 9) 0 2) DegreeTwoThreeSpectrum1959.graph sourceMap1292=true := by decide +kernel
theorem fusedMap1292_checked : acceptsGraphIso
    (fused (graph core1292) (root 9) 0 2) DegreeTwoThreeSpectrum1960.graph fusedMap1292=true := by decide +kernel
theorem certified1292 : Certified (graph core1292) (root 9) 0 2 :=
  of_native_maps core1292 DegreeTwoThreeSpectrum1959.graph DegreeTwoThreeSpectrum1960.graph
    sourceMap1292 fusedMap1292 sourceMap1292_checked fusedMap1292_checked
    DegreeTwoThreeFiniteComparisons.comparison1292
#print axioms sourceMap1292_checked
#print axioms fusedMap1292_checked
#print axioms certified1292
def sourceMap1292swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1292swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1292swap_checked : acceptsGraphIso
    (source (graph core1292) (root 9) 2 0) DegreeTwoThreeSpectrum1959.graph sourceMap1292swap=true := by decide +kernel
theorem fusedMap1292swap_checked : acceptsGraphIso
    (fused (graph core1292) (root 9) 2 0) DegreeTwoThreeSpectrum1960.graph fusedMap1292swap=true := by decide +kernel
theorem certified1292swap : Certified (graph core1292) (root 9) 2 0 :=
  of_native_maps core1292 DegreeTwoThreeSpectrum1959.graph DegreeTwoThreeSpectrum1960.graph
    sourceMap1292swap fusedMap1292swap sourceMap1292swap_checked fusedMap1292swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1292
#print axioms sourceMap1292swap_checked
#print axioms fusedMap1292swap_checked
#print axioms certified1292swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
