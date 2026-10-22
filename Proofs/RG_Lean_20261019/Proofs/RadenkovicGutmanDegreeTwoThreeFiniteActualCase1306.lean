/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1306 : Family 9 := level9.get ⟨372,by decide⟩
def sourceMap1306 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1306 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1306_checked : acceptsGraphIso
    (source (graph core1306) (root 9) 0 2) DegreeTwoThreeSpectrum2016.graph sourceMap1306=true := by decide +kernel
theorem fusedMap1306_checked : acceptsGraphIso
    (fused (graph core1306) (root 9) 0 2) DegreeTwoThreeSpectrum2018.graph fusedMap1306=true := by decide +kernel
theorem certified1306 : Certified (graph core1306) (root 9) 0 2 :=
  of_native_maps core1306 DegreeTwoThreeSpectrum2016.graph DegreeTwoThreeSpectrum2018.graph
    sourceMap1306 fusedMap1306 sourceMap1306_checked fusedMap1306_checked
    DegreeTwoThreeFiniteComparisons.comparison1306
#print axioms sourceMap1306_checked
#print axioms fusedMap1306_checked
#print axioms certified1306
def sourceMap1306swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1306swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1306swap_checked : acceptsGraphIso
    (source (graph core1306) (root 9) 2 0) DegreeTwoThreeSpectrum2016.graph sourceMap1306swap=true := by decide +kernel
theorem fusedMap1306swap_checked : acceptsGraphIso
    (fused (graph core1306) (root 9) 2 0) DegreeTwoThreeSpectrum2018.graph fusedMap1306swap=true := by decide +kernel
theorem certified1306swap : Certified (graph core1306) (root 9) 2 0 :=
  of_native_maps core1306 DegreeTwoThreeSpectrum2016.graph DegreeTwoThreeSpectrum2018.graph
    sourceMap1306swap fusedMap1306swap sourceMap1306swap_checked fusedMap1306swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1306
#print axioms sourceMap1306swap_checked
#print axioms fusedMap1306swap_checked
#print axioms certified1306swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
