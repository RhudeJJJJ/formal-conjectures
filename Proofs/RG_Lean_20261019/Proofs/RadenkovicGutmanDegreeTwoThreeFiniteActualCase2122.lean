/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2122 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap2122 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2122 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 0 4 v)
theorem sourceMap2122_checked : acceptsGraphIso
    (source (graph core2122) (root 8) 0 4) DegreeTwoThreeSpectrum2406.graph sourceMap2122=true := by decide +kernel
theorem fusedMap2122_checked : acceptsGraphIso
    (fused (graph core2122) (root 8) 0 4) DegreeTwoThreeSpectrum2407.graph fusedMap2122=true := by decide +kernel
theorem certified2122 : Certified (graph core2122) (root 8) 0 4 :=
  of_native_maps core2122 DegreeTwoThreeSpectrum2406.graph DegreeTwoThreeSpectrum2407.graph
    sourceMap2122 fusedMap2122 sourceMap2122_checked fusedMap2122_checked
    DegreeTwoThreeFiniteComparisons.comparison2122
#print axioms sourceMap2122_checked
#print axioms fusedMap2122_checked
#print axioms certified2122
def sourceMap2122swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2122swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 4 0 v)
theorem sourceMap2122swap_checked : acceptsGraphIso
    (source (graph core2122) (root 8) 4 0) DegreeTwoThreeSpectrum2406.graph sourceMap2122swap=true := by decide +kernel
theorem fusedMap2122swap_checked : acceptsGraphIso
    (fused (graph core2122) (root 8) 4 0) DegreeTwoThreeSpectrum2407.graph fusedMap2122swap=true := by decide +kernel
theorem certified2122swap : Certified (graph core2122) (root 8) 4 0 :=
  of_native_maps core2122 DegreeTwoThreeSpectrum2406.graph DegreeTwoThreeSpectrum2407.graph
    sourceMap2122swap fusedMap2122swap sourceMap2122swap_checked fusedMap2122swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2122
#print axioms sourceMap2122swap_checked
#print axioms fusedMap2122swap_checked
#print axioms certified2122swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
