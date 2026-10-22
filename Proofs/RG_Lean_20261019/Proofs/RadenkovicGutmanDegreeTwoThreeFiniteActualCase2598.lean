/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2598 : Family 10 := level10.get ⟨528,by decide⟩
def sourceMap2598 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2598 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2598_checked : acceptsGraphIso
    (source (graph core2598) (root 10) 0 4) DegreeTwoThreeSpectrum6105.graph sourceMap2598=true := by decide +kernel
theorem fusedMap2598_checked : acceptsGraphIso
    (fused (graph core2598) (root 10) 0 4) DegreeTwoThreeSpectrum5172.graph fusedMap2598=true := by decide +kernel
theorem certified2598 : Certified (graph core2598) (root 10) 0 4 :=
  of_native_maps core2598 DegreeTwoThreeSpectrum6105.graph DegreeTwoThreeSpectrum5172.graph
    sourceMap2598 fusedMap2598 sourceMap2598_checked fusedMap2598_checked
    DegreeTwoThreeFiniteComparisons.comparison2598
#print axioms sourceMap2598_checked
#print axioms fusedMap2598_checked
#print axioms certified2598
def sourceMap2598swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2598swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2598swap_checked : acceptsGraphIso
    (source (graph core2598) (root 10) 4 0) DegreeTwoThreeSpectrum6105.graph sourceMap2598swap=true := by decide +kernel
theorem fusedMap2598swap_checked : acceptsGraphIso
    (fused (graph core2598) (root 10) 4 0) DegreeTwoThreeSpectrum5172.graph fusedMap2598swap=true := by decide +kernel
theorem certified2598swap : Certified (graph core2598) (root 10) 4 0 :=
  of_native_maps core2598 DegreeTwoThreeSpectrum6105.graph DegreeTwoThreeSpectrum5172.graph
    sourceMap2598swap fusedMap2598swap sourceMap2598swap_checked fusedMap2598swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2598
#print axioms sourceMap2598swap_checked
#print axioms fusedMap2598swap_checked
#print axioms certified2598swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
