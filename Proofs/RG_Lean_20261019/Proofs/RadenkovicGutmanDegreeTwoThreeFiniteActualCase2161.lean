/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2161 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap2161 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2161 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2161_checked : acceptsGraphIso
    (source (graph core2161) (root 8) 0 4) DegreeTwoThreeSpectrum2696.graph sourceMap2161=true := by decide +kernel
theorem fusedMap2161_checked : acceptsGraphIso
    (fused (graph core2161) (root 8) 0 4) DegreeTwoThreeSpectrum2698.graph fusedMap2161=true := by decide +kernel
theorem certified2161 : Certified (graph core2161) (root 8) 0 4 :=
  of_native_maps core2161 DegreeTwoThreeSpectrum2696.graph DegreeTwoThreeSpectrum2698.graph
    sourceMap2161 fusedMap2161 sourceMap2161_checked fusedMap2161_checked
    DegreeTwoThreeFiniteComparisons.comparison2161
#print axioms sourceMap2161_checked
#print axioms fusedMap2161_checked
#print axioms certified2161
def sourceMap2161swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2161swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2161swap_checked : acceptsGraphIso
    (source (graph core2161) (root 8) 4 0) DegreeTwoThreeSpectrum2696.graph sourceMap2161swap=true := by decide +kernel
theorem fusedMap2161swap_checked : acceptsGraphIso
    (fused (graph core2161) (root 8) 4 0) DegreeTwoThreeSpectrum2698.graph fusedMap2161swap=true := by decide +kernel
theorem certified2161swap : Certified (graph core2161) (root 8) 4 0 :=
  of_native_maps core2161 DegreeTwoThreeSpectrum2696.graph DegreeTwoThreeSpectrum2698.graph
    sourceMap2161swap fusedMap2161swap sourceMap2161swap_checked fusedMap2161swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2161
#print axioms sourceMap2161swap_checked
#print axioms fusedMap2161swap_checked
#print axioms certified2161swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
