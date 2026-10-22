/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2188 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap2188 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2188 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2188_checked : acceptsGraphIso
    (source (graph core2188) (root 8) 0 4) DegreeTwoThreeSpectrum3123.graph sourceMap2188=true := by decide +kernel
theorem fusedMap2188_checked : acceptsGraphIso
    (fused (graph core2188) (root 8) 0 4) DegreeTwoThreeSpectrum2474.graph fusedMap2188=true := by decide +kernel
theorem certified2188 : Certified (graph core2188) (root 8) 0 4 :=
  of_native_maps core2188 DegreeTwoThreeSpectrum3123.graph DegreeTwoThreeSpectrum2474.graph
    sourceMap2188 fusedMap2188 sourceMap2188_checked fusedMap2188_checked
    DegreeTwoThreeFiniteComparisons.comparison2188
#print axioms sourceMap2188_checked
#print axioms fusedMap2188_checked
#print axioms certified2188
def sourceMap2188swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2188swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2188swap_checked : acceptsGraphIso
    (source (graph core2188) (root 8) 4 0) DegreeTwoThreeSpectrum3123.graph sourceMap2188swap=true := by decide +kernel
theorem fusedMap2188swap_checked : acceptsGraphIso
    (fused (graph core2188) (root 8) 4 0) DegreeTwoThreeSpectrum2474.graph fusedMap2188swap=true := by decide +kernel
theorem certified2188swap : Certified (graph core2188) (root 8) 4 0 :=
  of_native_maps core2188 DegreeTwoThreeSpectrum3123.graph DegreeTwoThreeSpectrum2474.graph
    sourceMap2188swap fusedMap2188swap sourceMap2188swap_checked fusedMap2188swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2188
#print axioms sourceMap2188swap_checked
#print axioms fusedMap2188swap_checked
#print axioms certified2188swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
