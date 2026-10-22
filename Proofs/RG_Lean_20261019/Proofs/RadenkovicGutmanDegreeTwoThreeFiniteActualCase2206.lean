/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2206 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap2206 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2206 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2206_checked : acceptsGraphIso
    (source (graph core2206) (root 8) 0 4) DegreeTwoThreeSpectrum3491.graph sourceMap2206=true := by decide +kernel
theorem fusedMap2206_checked : acceptsGraphIso
    (fused (graph core2206) (root 8) 0 4) DegreeTwoThreeSpectrum2702.graph fusedMap2206=true := by decide +kernel
theorem certified2206 : Certified (graph core2206) (root 8) 0 4 :=
  of_native_maps core2206 DegreeTwoThreeSpectrum3491.graph DegreeTwoThreeSpectrum2702.graph
    sourceMap2206 fusedMap2206 sourceMap2206_checked fusedMap2206_checked
    DegreeTwoThreeFiniteComparisons.comparison2206
#print axioms sourceMap2206_checked
#print axioms fusedMap2206_checked
#print axioms certified2206
def sourceMap2206swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2206swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2206swap_checked : acceptsGraphIso
    (source (graph core2206) (root 8) 4 0) DegreeTwoThreeSpectrum3491.graph sourceMap2206swap=true := by decide +kernel
theorem fusedMap2206swap_checked : acceptsGraphIso
    (fused (graph core2206) (root 8) 4 0) DegreeTwoThreeSpectrum2702.graph fusedMap2206swap=true := by decide +kernel
theorem certified2206swap : Certified (graph core2206) (root 8) 4 0 :=
  of_native_maps core2206 DegreeTwoThreeSpectrum3491.graph DegreeTwoThreeSpectrum2702.graph
    sourceMap2206swap fusedMap2206swap sourceMap2206swap_checked fusedMap2206swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2206
#print axioms sourceMap2206swap_checked
#print axioms fusedMap2206swap_checked
#print axioms certified2206swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
