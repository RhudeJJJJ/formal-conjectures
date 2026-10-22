/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1231 : Family 9 := level9.get ⟨160,by decide⟩
def sourceMap1231 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1231 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1231_checked : acceptsGraphIso
    (source (graph core1231) (root 9) 0 2) DegreeTwoThreeSpectrum2005.graph sourceMap1231=true := by decide +kernel
theorem fusedMap1231_checked : acceptsGraphIso
    (fused (graph core1231) (root 9) 0 2) DegreeTwoThreeSpectrum1760.graph fusedMap1231=true := by decide +kernel
theorem certified1231 : Certified (graph core1231) (root 9) 0 2 :=
  of_native_maps core1231 DegreeTwoThreeSpectrum2005.graph DegreeTwoThreeSpectrum1760.graph
    sourceMap1231 fusedMap1231 sourceMap1231_checked fusedMap1231_checked
    DegreeTwoThreeFiniteComparisons.comparison1231
#print axioms sourceMap1231_checked
#print axioms fusedMap1231_checked
#print axioms certified1231
def sourceMap1231swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1231swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1231swap_checked : acceptsGraphIso
    (source (graph core1231) (root 9) 2 0) DegreeTwoThreeSpectrum2005.graph sourceMap1231swap=true := by decide +kernel
theorem fusedMap1231swap_checked : acceptsGraphIso
    (fused (graph core1231) (root 9) 2 0) DegreeTwoThreeSpectrum1760.graph fusedMap1231swap=true := by decide +kernel
theorem certified1231swap : Certified (graph core1231) (root 9) 2 0 :=
  of_native_maps core1231 DegreeTwoThreeSpectrum2005.graph DegreeTwoThreeSpectrum1760.graph
    sourceMap1231swap fusedMap1231swap sourceMap1231swap_checked fusedMap1231swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1231
#print axioms sourceMap1231swap_checked
#print axioms fusedMap1231swap_checked
#print axioms certified1231swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
