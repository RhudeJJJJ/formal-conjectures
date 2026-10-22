/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2185 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap2185 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2185 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2185_checked : acceptsGraphIso
    (source (graph core2185) (root 8) 0 4) DegreeTwoThreeSpectrum3088.graph sourceMap2185=true := by decide +kernel
theorem fusedMap2185_checked : acceptsGraphIso
    (fused (graph core2185) (root 8) 0 4) DegreeTwoThreeSpectrum2460.graph fusedMap2185=true := by decide +kernel
theorem certified2185 : Certified (graph core2185) (root 8) 0 4 :=
  of_native_maps core2185 DegreeTwoThreeSpectrum3088.graph DegreeTwoThreeSpectrum2460.graph
    sourceMap2185 fusedMap2185 sourceMap2185_checked fusedMap2185_checked
    DegreeTwoThreeFiniteComparisons.comparison2185
#print axioms sourceMap2185_checked
#print axioms fusedMap2185_checked
#print axioms certified2185
def sourceMap2185swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2185swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2185swap_checked : acceptsGraphIso
    (source (graph core2185) (root 8) 4 0) DegreeTwoThreeSpectrum3088.graph sourceMap2185swap=true := by decide +kernel
theorem fusedMap2185swap_checked : acceptsGraphIso
    (fused (graph core2185) (root 8) 4 0) DegreeTwoThreeSpectrum2460.graph fusedMap2185swap=true := by decide +kernel
theorem certified2185swap : Certified (graph core2185) (root 8) 4 0 :=
  of_native_maps core2185 DegreeTwoThreeSpectrum3088.graph DegreeTwoThreeSpectrum2460.graph
    sourceMap2185swap fusedMap2185swap sourceMap2185swap_checked fusedMap2185swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2185
#print axioms sourceMap2185swap_checked
#print axioms fusedMap2185swap_checked
#print axioms certified2185swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
