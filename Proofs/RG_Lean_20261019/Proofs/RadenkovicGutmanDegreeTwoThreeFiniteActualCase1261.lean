/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1261 : Family 9 := level9.get ⟨248,by decide⟩
def sourceMap1261 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1261 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1261_checked : acceptsGraphIso
    (source (graph core1261) (root 9) 0 2) DegreeTwoThreeSpectrum2170.graph sourceMap1261=true := by decide +kernel
theorem fusedMap1261_checked : acceptsGraphIso
    (fused (graph core1261) (root 9) 0 2) DegreeTwoThreeSpectrum1855.graph fusedMap1261=true := by decide +kernel
theorem certified1261 : Certified (graph core1261) (root 9) 0 2 :=
  of_native_maps core1261 DegreeTwoThreeSpectrum2170.graph DegreeTwoThreeSpectrum1855.graph
    sourceMap1261 fusedMap1261 sourceMap1261_checked fusedMap1261_checked
    DegreeTwoThreeFiniteComparisons.comparison1261
#print axioms sourceMap1261_checked
#print axioms fusedMap1261_checked
#print axioms certified1261
def sourceMap1261swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1261swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1261swap_checked : acceptsGraphIso
    (source (graph core1261) (root 9) 2 0) DegreeTwoThreeSpectrum2170.graph sourceMap1261swap=true := by decide +kernel
theorem fusedMap1261swap_checked : acceptsGraphIso
    (fused (graph core1261) (root 9) 2 0) DegreeTwoThreeSpectrum1855.graph fusedMap1261swap=true := by decide +kernel
theorem certified1261swap : Certified (graph core1261) (root 9) 2 0 :=
  of_native_maps core1261 DegreeTwoThreeSpectrum2170.graph DegreeTwoThreeSpectrum1855.graph
    sourceMap1261swap fusedMap1261swap sourceMap1261swap_checked fusedMap1261swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1261
#print axioms sourceMap1261swap_checked
#print axioms fusedMap1261swap_checked
#print axioms certified1261swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
