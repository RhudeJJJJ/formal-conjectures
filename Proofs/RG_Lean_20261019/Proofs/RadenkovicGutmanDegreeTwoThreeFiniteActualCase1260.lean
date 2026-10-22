/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1260 : Family 9 := level9.get ⟨247,by decide⟩
def sourceMap1260 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1260 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1260_checked : acceptsGraphIso
    (source (graph core1260) (root 9) 0 2) DegreeTwoThreeSpectrum2168.graph sourceMap1260=true := by decide +kernel
theorem fusedMap1260_checked : acceptsGraphIso
    (fused (graph core1260) (root 9) 0 2) DegreeTwoThreeSpectrum1854.graph fusedMap1260=true := by decide +kernel
theorem certified1260 : Certified (graph core1260) (root 9) 0 2 :=
  of_native_maps core1260 DegreeTwoThreeSpectrum2168.graph DegreeTwoThreeSpectrum1854.graph
    sourceMap1260 fusedMap1260 sourceMap1260_checked fusedMap1260_checked
    DegreeTwoThreeFiniteComparisons.comparison1260
#print axioms sourceMap1260_checked
#print axioms fusedMap1260_checked
#print axioms certified1260
def sourceMap1260swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1260swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1260swap_checked : acceptsGraphIso
    (source (graph core1260) (root 9) 2 0) DegreeTwoThreeSpectrum2168.graph sourceMap1260swap=true := by decide +kernel
theorem fusedMap1260swap_checked : acceptsGraphIso
    (fused (graph core1260) (root 9) 2 0) DegreeTwoThreeSpectrum1854.graph fusedMap1260swap=true := by decide +kernel
theorem certified1260swap : Certified (graph core1260) (root 9) 2 0 :=
  of_native_maps core1260 DegreeTwoThreeSpectrum2168.graph DegreeTwoThreeSpectrum1854.graph
    sourceMap1260swap fusedMap1260swap sourceMap1260swap_checked fusedMap1260swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1260
#print axioms sourceMap1260swap_checked
#print axioms fusedMap1260swap_checked
#print axioms certified1260swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
