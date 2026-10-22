/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2542 : Family 10 := level10.get ⟨358,by decide⟩
def sourceMap2542 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2542 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2542_checked : acceptsGraphIso
    (source (graph core2542) (root 10) 0 4) DegreeTwoThreeSpectrum5639.graph sourceMap2542=true := by decide +kernel
theorem fusedMap2542_checked : acceptsGraphIso
    (fused (graph core2542) (root 10) 0 4) DegreeTwoThreeSpectrum5640.graph fusedMap2542=true := by decide +kernel
theorem certified2542 : Certified (graph core2542) (root 10) 0 4 :=
  of_native_maps core2542 DegreeTwoThreeSpectrum5639.graph DegreeTwoThreeSpectrum5640.graph
    sourceMap2542 fusedMap2542 sourceMap2542_checked fusedMap2542_checked
    DegreeTwoThreeFiniteComparisons.comparison2542
#print axioms sourceMap2542_checked
#print axioms fusedMap2542_checked
#print axioms certified2542
def sourceMap2542swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2542swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2542swap_checked : acceptsGraphIso
    (source (graph core2542) (root 10) 4 0) DegreeTwoThreeSpectrum5639.graph sourceMap2542swap=true := by decide +kernel
theorem fusedMap2542swap_checked : acceptsGraphIso
    (fused (graph core2542) (root 10) 4 0) DegreeTwoThreeSpectrum5640.graph fusedMap2542swap=true := by decide +kernel
theorem certified2542swap : Certified (graph core2542) (root 10) 4 0 :=
  of_native_maps core2542 DegreeTwoThreeSpectrum5639.graph DegreeTwoThreeSpectrum5640.graph
    sourceMap2542swap fusedMap2542swap sourceMap2542swap_checked fusedMap2542swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2542
#print axioms sourceMap2542swap_checked
#print axioms fusedMap2542swap_checked
#print axioms certified2542swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
