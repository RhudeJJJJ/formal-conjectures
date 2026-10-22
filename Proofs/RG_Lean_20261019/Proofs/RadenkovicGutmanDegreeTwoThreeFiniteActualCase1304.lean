/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1304 : Family 9 := level9.get ⟨368,by decide⟩
def sourceMap1304 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1304 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1304_checked : acceptsGraphIso
    (source (graph core1304) (root 9) 0 2) DegreeTwoThreeSpectrum2009.graph sourceMap1304=true := by decide +kernel
theorem fusedMap1304_checked : acceptsGraphIso
    (fused (graph core1304) (root 9) 0 2) DegreeTwoThreeSpectrum2010.graph fusedMap1304=true := by decide +kernel
theorem certified1304 : Certified (graph core1304) (root 9) 0 2 :=
  of_native_maps core1304 DegreeTwoThreeSpectrum2009.graph DegreeTwoThreeSpectrum2010.graph
    sourceMap1304 fusedMap1304 sourceMap1304_checked fusedMap1304_checked
    DegreeTwoThreeFiniteComparisons.comparison1304
#print axioms sourceMap1304_checked
#print axioms fusedMap1304_checked
#print axioms certified1304
def sourceMap1304swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1304swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1304swap_checked : acceptsGraphIso
    (source (graph core1304) (root 9) 2 0) DegreeTwoThreeSpectrum2009.graph sourceMap1304swap=true := by decide +kernel
theorem fusedMap1304swap_checked : acceptsGraphIso
    (fused (graph core1304) (root 9) 2 0) DegreeTwoThreeSpectrum2010.graph fusedMap1304swap=true := by decide +kernel
theorem certified1304swap : Certified (graph core1304) (root 9) 2 0 :=
  of_native_maps core1304 DegreeTwoThreeSpectrum2009.graph DegreeTwoThreeSpectrum2010.graph
    sourceMap1304swap fusedMap1304swap sourceMap1304swap_checked fusedMap1304swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1304
#print axioms sourceMap1304swap_checked
#print axioms fusedMap1304swap_checked
#print axioms certified1304swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
