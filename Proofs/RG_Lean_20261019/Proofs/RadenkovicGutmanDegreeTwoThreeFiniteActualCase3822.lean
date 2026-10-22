/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3822 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap3822 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3822 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3822_checked : acceptsGraphIso
    (source (graph core3822) (root 7) 1 4) DegreeTwoThreeSpectrum3546.graph sourceMap3822=true := by decide +kernel
theorem fusedMap3822_checked : acceptsGraphIso
    (fused (graph core3822) (root 7) 1 4) DegreeTwoThreeSpectrum2738.graph fusedMap3822=true := by decide +kernel
theorem certified3822 : Certified (graph core3822) (root 7) 1 4 :=
  of_native_maps core3822 DegreeTwoThreeSpectrum3546.graph DegreeTwoThreeSpectrum2738.graph
    sourceMap3822 fusedMap3822 sourceMap3822_checked fusedMap3822_checked
    DegreeTwoThreeFiniteComparisons.comparison3822
#print axioms sourceMap3822_checked
#print axioms fusedMap3822_checked
#print axioms certified3822
def sourceMap3822swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3822swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3822swap_checked : acceptsGraphIso
    (source (graph core3822) (root 7) 4 1) DegreeTwoThreeSpectrum3546.graph sourceMap3822swap=true := by decide +kernel
theorem fusedMap3822swap_checked : acceptsGraphIso
    (fused (graph core3822) (root 7) 4 1) DegreeTwoThreeSpectrum2738.graph fusedMap3822swap=true := by decide +kernel
theorem certified3822swap : Certified (graph core3822) (root 7) 4 1 :=
  of_native_maps core3822 DegreeTwoThreeSpectrum3546.graph DegreeTwoThreeSpectrum2738.graph
    sourceMap3822swap fusedMap3822swap sourceMap3822swap_checked fusedMap3822swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3822
#print axioms sourceMap3822swap_checked
#print axioms fusedMap3822swap_checked
#print axioms certified3822swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
