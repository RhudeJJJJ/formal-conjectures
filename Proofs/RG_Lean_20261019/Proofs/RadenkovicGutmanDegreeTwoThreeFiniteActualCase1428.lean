/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1428 : Family 9 := level9.get ⟨691,by decide⟩
def sourceMap1428 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 0 2 v)
def fusedMap1428 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1428_checked : acceptsGraphIso
    (source (graph core1428) (root 9) 0 2) DegreeTwoThreeSpectrum2241.graph sourceMap1428=true := by decide +kernel
theorem fusedMap1428_checked : acceptsGraphIso
    (fused (graph core1428) (root 9) 0 2) DegreeTwoThreeSpectrum2242.graph fusedMap1428=true := by decide +kernel
theorem certified1428 : Certified (graph core1428) (root 9) 0 2 :=
  of_native_maps core1428 DegreeTwoThreeSpectrum2241.graph DegreeTwoThreeSpectrum2242.graph
    sourceMap1428 fusedMap1428 sourceMap1428_checked fusedMap1428_checked
    DegreeTwoThreeFiniteComparisons.comparison1428
#print axioms sourceMap1428_checked
#print axioms fusedMap1428_checked
#print axioms certified1428
def sourceMap1428swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,10] (sourceLabel 9 2 0 v)
def fusedMap1428swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1428swap_checked : acceptsGraphIso
    (source (graph core1428) (root 9) 2 0) DegreeTwoThreeSpectrum2241.graph sourceMap1428swap=true := by decide +kernel
theorem fusedMap1428swap_checked : acceptsGraphIso
    (fused (graph core1428) (root 9) 2 0) DegreeTwoThreeSpectrum2242.graph fusedMap1428swap=true := by decide +kernel
theorem certified1428swap : Certified (graph core1428) (root 9) 2 0 :=
  of_native_maps core1428 DegreeTwoThreeSpectrum2241.graph DegreeTwoThreeSpectrum2242.graph
    sourceMap1428swap fusedMap1428swap sourceMap1428swap_checked fusedMap1428swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1428
#print axioms sourceMap1428swap_checked
#print axioms fusedMap1428swap_checked
#print axioms certified1428swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
