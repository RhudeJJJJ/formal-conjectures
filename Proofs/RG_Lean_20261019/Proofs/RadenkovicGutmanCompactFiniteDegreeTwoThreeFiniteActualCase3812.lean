/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3812 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap3812 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3812 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3812_checked : acceptsGraphIso
    (source (graph core3812) (root 7) 1 4) DegreeTwoThreeSpectrum3191.graph sourceMap3812=true := by decide +kernel
theorem fusedMap3812_checked : acceptsGraphIso
    (fused (graph core3812) (root 7) 1 4) DegreeTwoThreeSpectrum2513.graph fusedMap3812=true := by decide +kernel
theorem certified3812 : Certified (graph core3812) (root 7) 1 4 :=
  of_native_maps core3812 DegreeTwoThreeSpectrum3191.graph DegreeTwoThreeSpectrum2513.graph
    sourceMap3812 fusedMap3812 sourceMap3812_checked fusedMap3812_checked
    DegreeTwoThreeFiniteComparisons.comparison3812
#print axioms sourceMap3812_checked
#print axioms fusedMap3812_checked
#print axioms certified3812
def sourceMap3812swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3812swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3812swap_checked : acceptsGraphIso
    (source (graph core3812) (root 7) 4 1) DegreeTwoThreeSpectrum3191.graph sourceMap3812swap=true := by decide +kernel
theorem fusedMap3812swap_checked : acceptsGraphIso
    (fused (graph core3812) (root 7) 4 1) DegreeTwoThreeSpectrum2513.graph fusedMap3812swap=true := by decide +kernel
theorem certified3812swap : Certified (graph core3812) (root 7) 4 1 :=
  of_native_maps core3812 DegreeTwoThreeSpectrum3191.graph DegreeTwoThreeSpectrum2513.graph
    sourceMap3812swap fusedMap3812swap sourceMap3812swap_checked fusedMap3812swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3812
#print axioms sourceMap3812swap_checked
#print axioms fusedMap3812swap_checked
#print axioms certified3812swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
