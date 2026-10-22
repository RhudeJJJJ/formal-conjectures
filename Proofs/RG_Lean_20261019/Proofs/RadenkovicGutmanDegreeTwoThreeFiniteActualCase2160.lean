/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2160 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap2160 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2160 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2160_checked : acceptsGraphIso
    (source (graph core2160) (root 8) 0 4) DegreeTwoThreeSpectrum2674.graph sourceMap2160=true := by decide +kernel
theorem fusedMap2160_checked : acceptsGraphIso
    (fused (graph core2160) (root 8) 0 4) DegreeTwoThreeSpectrum2676.graph fusedMap2160=true := by decide +kernel
theorem certified2160 : Certified (graph core2160) (root 8) 0 4 :=
  of_native_maps core2160 DegreeTwoThreeSpectrum2674.graph DegreeTwoThreeSpectrum2676.graph
    sourceMap2160 fusedMap2160 sourceMap2160_checked fusedMap2160_checked
    DegreeTwoThreeFiniteComparisons.comparison2160
#print axioms sourceMap2160_checked
#print axioms fusedMap2160_checked
#print axioms certified2160
def sourceMap2160swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2160swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2160swap_checked : acceptsGraphIso
    (source (graph core2160) (root 8) 4 0) DegreeTwoThreeSpectrum2674.graph sourceMap2160swap=true := by decide +kernel
theorem fusedMap2160swap_checked : acceptsGraphIso
    (fused (graph core2160) (root 8) 4 0) DegreeTwoThreeSpectrum2676.graph fusedMap2160swap=true := by decide +kernel
theorem certified2160swap : Certified (graph core2160) (root 8) 4 0 :=
  of_native_maps core2160 DegreeTwoThreeSpectrum2674.graph DegreeTwoThreeSpectrum2676.graph
    sourceMap2160swap fusedMap2160swap sourceMap2160swap_checked fusedMap2160swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2160
#print axioms sourceMap2160swap_checked
#print axioms fusedMap2160swap_checked
#print axioms certified2160swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
