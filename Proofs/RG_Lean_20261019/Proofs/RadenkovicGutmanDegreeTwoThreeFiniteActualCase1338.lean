/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1338 : Family 9 := level9.get ⟨452,by decide⟩
def sourceMap1338 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1338 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1338_checked : acceptsGraphIso
    (source (graph core1338) (root 9) 0 2) DegreeTwoThreeSpectrum2132.graph sourceMap1338=true := by decide +kernel
theorem fusedMap1338_checked : acceptsGraphIso
    (fused (graph core1338) (root 9) 0 2) DegreeTwoThreeSpectrum2134.graph fusedMap1338=true := by decide +kernel
theorem certified1338 : Certified (graph core1338) (root 9) 0 2 :=
  of_native_maps core1338 DegreeTwoThreeSpectrum2132.graph DegreeTwoThreeSpectrum2134.graph
    sourceMap1338 fusedMap1338 sourceMap1338_checked fusedMap1338_checked
    DegreeTwoThreeFiniteComparisons.comparison1338
#print axioms sourceMap1338_checked
#print axioms fusedMap1338_checked
#print axioms certified1338
def sourceMap1338swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1338swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1338swap_checked : acceptsGraphIso
    (source (graph core1338) (root 9) 2 0) DegreeTwoThreeSpectrum2132.graph sourceMap1338swap=true := by decide +kernel
theorem fusedMap1338swap_checked : acceptsGraphIso
    (fused (graph core1338) (root 9) 2 0) DegreeTwoThreeSpectrum2134.graph fusedMap1338swap=true := by decide +kernel
theorem certified1338swap : Certified (graph core1338) (root 9) 2 0 :=
  of_native_maps core1338 DegreeTwoThreeSpectrum2132.graph DegreeTwoThreeSpectrum2134.graph
    sourceMap1338swap fusedMap1338swap sourceMap1338swap_checked fusedMap1338swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1338
#print axioms sourceMap1338swap_checked
#print axioms fusedMap1338swap_checked
#print axioms certified1338swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
