/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2659 : Family 10 := level10.get ⟨707,by decide⟩
def sourceMap2659 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2659 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2659_checked : acceptsGraphIso
    (source (graph core2659) (root 10) 0 4) DegreeTwoThreeSpectrum6551.graph sourceMap2659=true := by decide +kernel
theorem fusedMap2659_checked : acceptsGraphIso
    (fused (graph core2659) (root 10) 0 4) DegreeTwoThreeSpectrum5448.graph fusedMap2659=true := by decide +kernel
theorem certified2659 : Certified (graph core2659) (root 10) 0 4 :=
  of_native_maps core2659 DegreeTwoThreeSpectrum6551.graph DegreeTwoThreeSpectrum5448.graph
    sourceMap2659 fusedMap2659 sourceMap2659_checked fusedMap2659_checked
    DegreeTwoThreeFiniteComparisons.comparison2659
#print axioms sourceMap2659_checked
#print axioms fusedMap2659_checked
#print axioms certified2659
def sourceMap2659swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2659swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2659swap_checked : acceptsGraphIso
    (source (graph core2659) (root 10) 4 0) DegreeTwoThreeSpectrum6551.graph sourceMap2659swap=true := by decide +kernel
theorem fusedMap2659swap_checked : acceptsGraphIso
    (fused (graph core2659) (root 10) 4 0) DegreeTwoThreeSpectrum5448.graph fusedMap2659swap=true := by decide +kernel
theorem certified2659swap : Certified (graph core2659) (root 10) 4 0 :=
  of_native_maps core2659 DegreeTwoThreeSpectrum6551.graph DegreeTwoThreeSpectrum5448.graph
    sourceMap2659swap fusedMap2659swap sourceMap2659swap_checked fusedMap2659swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2659
#print axioms sourceMap2659swap_checked
#print axioms fusedMap2659swap_checked
#print axioms certified2659swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
