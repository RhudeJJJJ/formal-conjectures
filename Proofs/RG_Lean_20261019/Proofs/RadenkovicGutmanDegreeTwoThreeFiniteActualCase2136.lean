/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2136 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap2136 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2136 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2136_checked : acceptsGraphIso
    (source (graph core2136) (root 8) 0 4) DegreeTwoThreeSpectrum2871.graph sourceMap2136=true := by decide +kernel
theorem fusedMap2136_checked : acceptsGraphIso
    (fused (graph core2136) (root 8) 0 4) DegreeTwoThreeSpectrum2385.graph fusedMap2136=true := by decide +kernel
theorem certified2136 : Certified (graph core2136) (root 8) 0 4 :=
  of_native_maps core2136 DegreeTwoThreeSpectrum2871.graph DegreeTwoThreeSpectrum2385.graph
    sourceMap2136 fusedMap2136 sourceMap2136_checked fusedMap2136_checked
    DegreeTwoThreeFiniteComparisons.comparison2136
#print axioms sourceMap2136_checked
#print axioms fusedMap2136_checked
#print axioms certified2136
def sourceMap2136swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2136swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2136swap_checked : acceptsGraphIso
    (source (graph core2136) (root 8) 4 0) DegreeTwoThreeSpectrum2871.graph sourceMap2136swap=true := by decide +kernel
theorem fusedMap2136swap_checked : acceptsGraphIso
    (fused (graph core2136) (root 8) 4 0) DegreeTwoThreeSpectrum2385.graph fusedMap2136swap=true := by decide +kernel
theorem certified2136swap : Certified (graph core2136) (root 8) 4 0 :=
  of_native_maps core2136 DegreeTwoThreeSpectrum2871.graph DegreeTwoThreeSpectrum2385.graph
    sourceMap2136swap fusedMap2136swap sourceMap2136swap_checked fusedMap2136swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2136
#print axioms sourceMap2136swap_checked
#print axioms fusedMap2136swap_checked
#print axioms certified2136swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
