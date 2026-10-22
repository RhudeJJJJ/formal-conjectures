/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2582 : Family 10 := level10.get ⟨478,by decide⟩
def sourceMap2582 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,6,7,8,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2582 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2582_checked : acceptsGraphIso
    (source (graph core2582) (root 10) 0 4) DegreeTwoThreeSpectrum5937.graph sourceMap2582=true := by decide +kernel
theorem fusedMap2582_checked : acceptsGraphIso
    (fused (graph core2582) (root 10) 0 4) DegreeTwoThreeSpectrum5942.graph fusedMap2582=true := by decide +kernel
theorem certified2582 : Certified (graph core2582) (root 10) 0 4 :=
  of_native_maps core2582 DegreeTwoThreeSpectrum5937.graph DegreeTwoThreeSpectrum5942.graph
    sourceMap2582 fusedMap2582 sourceMap2582_checked fusedMap2582_checked
    DegreeTwoThreeFiniteComparisons.comparison2582
#print axioms sourceMap2582_checked
#print axioms fusedMap2582_checked
#print axioms certified2582
def sourceMap2582swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,6,7,1,2,3,4,5,8] (sourceLabel 10 4 0 v)
def fusedMap2582swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2582swap_checked : acceptsGraphIso
    (source (graph core2582) (root 10) 4 0) DegreeTwoThreeSpectrum5937.graph sourceMap2582swap=true := by decide +kernel
theorem fusedMap2582swap_checked : acceptsGraphIso
    (fused (graph core2582) (root 10) 4 0) DegreeTwoThreeSpectrum5942.graph fusedMap2582swap=true := by decide +kernel
theorem certified2582swap : Certified (graph core2582) (root 10) 4 0 :=
  of_native_maps core2582 DegreeTwoThreeSpectrum5937.graph DegreeTwoThreeSpectrum5942.graph
    sourceMap2582swap fusedMap2582swap sourceMap2582swap_checked fusedMap2582swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2582
#print axioms sourceMap2582swap_checked
#print axioms fusedMap2582swap_checked
#print axioms certified2582swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
