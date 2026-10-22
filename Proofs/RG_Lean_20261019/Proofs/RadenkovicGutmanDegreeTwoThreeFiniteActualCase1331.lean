/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1331 : Family 9 := level9.get ⟨434,by decide⟩
def sourceMap1331 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1331 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1331_checked : acceptsGraphIso
    (source (graph core1331) (root 9) 0 2) DegreeTwoThreeSpectrum2106.graph sourceMap1331=true := by decide +kernel
theorem fusedMap1331_checked : acceptsGraphIso
    (fused (graph core1331) (root 9) 0 2) DegreeTwoThreeSpectrum2110.graph fusedMap1331=true := by decide +kernel
theorem certified1331 : Certified (graph core1331) (root 9) 0 2 :=
  of_native_maps core1331 DegreeTwoThreeSpectrum2106.graph DegreeTwoThreeSpectrum2110.graph
    sourceMap1331 fusedMap1331 sourceMap1331_checked fusedMap1331_checked
    DegreeTwoThreeFiniteComparisons.comparison1331
#print axioms sourceMap1331_checked
#print axioms fusedMap1331_checked
#print axioms certified1331
def sourceMap1331swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1331swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1331swap_checked : acceptsGraphIso
    (source (graph core1331) (root 9) 2 0) DegreeTwoThreeSpectrum2106.graph sourceMap1331swap=true := by decide +kernel
theorem fusedMap1331swap_checked : acceptsGraphIso
    (fused (graph core1331) (root 9) 2 0) DegreeTwoThreeSpectrum2110.graph fusedMap1331swap=true := by decide +kernel
theorem certified1331swap : Certified (graph core1331) (root 9) 2 0 :=
  of_native_maps core1331 DegreeTwoThreeSpectrum2106.graph DegreeTwoThreeSpectrum2110.graph
    sourceMap1331swap fusedMap1331swap sourceMap1331swap_checked fusedMap1331swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1331
#print axioms sourceMap1331swap_checked
#print axioms fusedMap1331swap_checked
#print axioms certified1331swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
