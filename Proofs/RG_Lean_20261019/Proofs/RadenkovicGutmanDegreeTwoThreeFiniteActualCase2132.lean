/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2132 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap2132 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2132 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2132_checked : acceptsGraphIso
    (source (graph core2132) (root 8) 0 4) DegreeTwoThreeSpectrum2730.graph sourceMap2132=true := by decide +kernel
theorem fusedMap2132_checked : acceptsGraphIso
    (fused (graph core2132) (root 8) 0 4) DegreeTwoThreeSpectrum2357.graph fusedMap2132=true := by decide +kernel
theorem certified2132 : Certified (graph core2132) (root 8) 0 4 :=
  of_native_maps core2132 DegreeTwoThreeSpectrum2730.graph DegreeTwoThreeSpectrum2357.graph
    sourceMap2132 fusedMap2132 sourceMap2132_checked fusedMap2132_checked
    DegreeTwoThreeFiniteComparisons.comparison2132
#print axioms sourceMap2132_checked
#print axioms fusedMap2132_checked
#print axioms certified2132
def sourceMap2132swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2132swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2132swap_checked : acceptsGraphIso
    (source (graph core2132) (root 8) 4 0) DegreeTwoThreeSpectrum2730.graph sourceMap2132swap=true := by decide +kernel
theorem fusedMap2132swap_checked : acceptsGraphIso
    (fused (graph core2132) (root 8) 4 0) DegreeTwoThreeSpectrum2357.graph fusedMap2132swap=true := by decide +kernel
theorem certified2132swap : Certified (graph core2132) (root 8) 4 0 :=
  of_native_maps core2132 DegreeTwoThreeSpectrum2730.graph DegreeTwoThreeSpectrum2357.graph
    sourceMap2132swap fusedMap2132swap sourceMap2132swap_checked fusedMap2132swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2132
#print axioms sourceMap2132swap_checked
#print axioms fusedMap2132swap_checked
#print axioms certified2132swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
