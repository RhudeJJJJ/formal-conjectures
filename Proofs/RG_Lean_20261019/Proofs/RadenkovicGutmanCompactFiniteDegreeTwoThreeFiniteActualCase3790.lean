/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3790 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap3790 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,8,6,7,1,2,3,4,5] (sourceLabel 7 1 4 v)
def fusedMap3790 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3790_checked : acceptsGraphIso
    (source (graph core3790) (root 7) 1 4) DegreeTwoThreeSpectrum2430.graph sourceMap3790=true := by decide +kernel
theorem fusedMap3790_checked : acceptsGraphIso
    (fused (graph core3790) (root 7) 1 4) DegreeTwoThreeSpectrum2314.graph fusedMap3790=true := by decide +kernel
theorem certified3790 : Certified (graph core3790) (root 7) 1 4 :=
  of_native_maps core3790 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap3790 fusedMap3790 sourceMap3790_checked fusedMap3790_checked
    DegreeTwoThreeFiniteComparisons.comparison3790
#print axioms sourceMap3790_checked
#print axioms fusedMap3790_checked
#print axioms certified3790
def sourceMap3790swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,8,1,2,3,4,5,6,7] (sourceLabel 7 4 1 v)
def fusedMap3790swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3790swap_checked : acceptsGraphIso
    (source (graph core3790) (root 7) 4 1) DegreeTwoThreeSpectrum2430.graph sourceMap3790swap=true := by decide +kernel
theorem fusedMap3790swap_checked : acceptsGraphIso
    (fused (graph core3790) (root 7) 4 1) DegreeTwoThreeSpectrum2314.graph fusedMap3790swap=true := by decide +kernel
theorem certified3790swap : Certified (graph core3790) (root 7) 4 1 :=
  of_native_maps core3790 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap3790swap fusedMap3790swap sourceMap3790swap_checked fusedMap3790swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3790
#print axioms sourceMap3790swap_checked
#print axioms fusedMap3790swap_checked
#print axioms certified3790swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
