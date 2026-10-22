/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2685 : Family 10 := level10.get ⟨782,by decide⟩
def sourceMap2685 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2685 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2685_checked : acceptsGraphIso
    (source (graph core2685) (root 10) 0 4) DegreeTwoThreeSpectrum6718.graph sourceMap2685=true := by decide +kernel
theorem fusedMap2685_checked : acceptsGraphIso
    (fused (graph core2685) (root 10) 0 4) DegreeTwoThreeSpectrum5563.graph fusedMap2685=true := by decide +kernel
theorem certified2685 : Certified (graph core2685) (root 10) 0 4 :=
  of_native_maps core2685 DegreeTwoThreeSpectrum6718.graph DegreeTwoThreeSpectrum5563.graph
    sourceMap2685 fusedMap2685 sourceMap2685_checked fusedMap2685_checked
    DegreeTwoThreeFiniteComparisons.comparison2685
#print axioms sourceMap2685_checked
#print axioms fusedMap2685_checked
#print axioms certified2685
def sourceMap2685swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2685swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2685swap_checked : acceptsGraphIso
    (source (graph core2685) (root 10) 4 0) DegreeTwoThreeSpectrum6718.graph sourceMap2685swap=true := by decide +kernel
theorem fusedMap2685swap_checked : acceptsGraphIso
    (fused (graph core2685) (root 10) 4 0) DegreeTwoThreeSpectrum5563.graph fusedMap2685swap=true := by decide +kernel
theorem certified2685swap : Certified (graph core2685) (root 10) 4 0 :=
  of_native_maps core2685 DegreeTwoThreeSpectrum6718.graph DegreeTwoThreeSpectrum5563.graph
    sourceMap2685swap fusedMap2685swap sourceMap2685swap_checked fusedMap2685swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2685
#print axioms sourceMap2685swap_checked
#print axioms fusedMap2685swap_checked
#print axioms certified2685swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
