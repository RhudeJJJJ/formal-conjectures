/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3803 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap3803 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3803 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3803_checked : acceptsGraphIso
    (source (graph core3803) (root 7) 1 4) DegreeTwoThreeSpectrum2778.graph sourceMap3803=true := by decide +kernel
theorem fusedMap3803_checked : acceptsGraphIso
    (fused (graph core3803) (root 7) 1 4) DegreeTwoThreeSpectrum2366.graph fusedMap3803=true := by decide +kernel
theorem certified3803 : Certified (graph core3803) (root 7) 1 4 :=
  of_native_maps core3803 DegreeTwoThreeSpectrum2778.graph DegreeTwoThreeSpectrum2366.graph
    sourceMap3803 fusedMap3803 sourceMap3803_checked fusedMap3803_checked
    DegreeTwoThreeFiniteComparisons.comparison3803
#print axioms sourceMap3803_checked
#print axioms fusedMap3803_checked
#print axioms certified3803
def sourceMap3803swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3803swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3803swap_checked : acceptsGraphIso
    (source (graph core3803) (root 7) 4 1) DegreeTwoThreeSpectrum2778.graph sourceMap3803swap=true := by decide +kernel
theorem fusedMap3803swap_checked : acceptsGraphIso
    (fused (graph core3803) (root 7) 4 1) DegreeTwoThreeSpectrum2366.graph fusedMap3803swap=true := by decide +kernel
theorem certified3803swap : Certified (graph core3803) (root 7) 4 1 :=
  of_native_maps core3803 DegreeTwoThreeSpectrum2778.graph DegreeTwoThreeSpectrum2366.graph
    sourceMap3803swap fusedMap3803swap sourceMap3803swap_checked fusedMap3803swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3803
#print axioms sourceMap3803swap_checked
#print axioms fusedMap3803swap_checked
#print axioms certified3803swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
