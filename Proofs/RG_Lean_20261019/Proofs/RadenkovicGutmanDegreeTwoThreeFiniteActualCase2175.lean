/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2175 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap2175 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2175 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2175_checked : acceptsGraphIso
    (source (graph core2175) (root 8) 0 4) DegreeTwoThreeSpectrum2911.graph sourceMap2175=true := by decide +kernel
theorem fusedMap2175_checked : acceptsGraphIso
    (fused (graph core2175) (root 8) 0 4) DegreeTwoThreeSpectrum2913.graph fusedMap2175=true := by decide +kernel
theorem certified2175 : Certified (graph core2175) (root 8) 0 4 :=
  of_native_maps core2175 DegreeTwoThreeSpectrum2911.graph DegreeTwoThreeSpectrum2913.graph
    sourceMap2175 fusedMap2175 sourceMap2175_checked fusedMap2175_checked
    DegreeTwoThreeFiniteComparisons.comparison2175
#print axioms sourceMap2175_checked
#print axioms fusedMap2175_checked
#print axioms certified2175
def sourceMap2175swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2175swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2175swap_checked : acceptsGraphIso
    (source (graph core2175) (root 8) 4 0) DegreeTwoThreeSpectrum2911.graph sourceMap2175swap=true := by decide +kernel
theorem fusedMap2175swap_checked : acceptsGraphIso
    (fused (graph core2175) (root 8) 4 0) DegreeTwoThreeSpectrum2913.graph fusedMap2175swap=true := by decide +kernel
theorem certified2175swap : Certified (graph core2175) (root 8) 4 0 :=
  of_native_maps core2175 DegreeTwoThreeSpectrum2911.graph DegreeTwoThreeSpectrum2913.graph
    sourceMap2175swap fusedMap2175swap sourceMap2175swap_checked fusedMap2175swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2175
#print axioms sourceMap2175swap_checked
#print axioms fusedMap2175swap_checked
#print axioms certified2175swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
