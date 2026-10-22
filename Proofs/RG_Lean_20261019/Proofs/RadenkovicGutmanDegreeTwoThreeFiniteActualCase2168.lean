/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2168 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap2168 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2168 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2168_checked : acceptsGraphIso
    (source (graph core2168) (root 8) 0 4) DegreeTwoThreeSpectrum2775.graph sourceMap2168=true := by decide +kernel
theorem fusedMap2168_checked : acceptsGraphIso
    (fused (graph core2168) (root 8) 0 4) DegreeTwoThreeSpectrum2777.graph fusedMap2168=true := by decide +kernel
theorem certified2168 : Certified (graph core2168) (root 8) 0 4 :=
  of_native_maps core2168 DegreeTwoThreeSpectrum2775.graph DegreeTwoThreeSpectrum2777.graph
    sourceMap2168 fusedMap2168 sourceMap2168_checked fusedMap2168_checked
    DegreeTwoThreeFiniteComparisons.comparison2168
#print axioms sourceMap2168_checked
#print axioms fusedMap2168_checked
#print axioms certified2168
def sourceMap2168swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2168swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2168swap_checked : acceptsGraphIso
    (source (graph core2168) (root 8) 4 0) DegreeTwoThreeSpectrum2775.graph sourceMap2168swap=true := by decide +kernel
theorem fusedMap2168swap_checked : acceptsGraphIso
    (fused (graph core2168) (root 8) 4 0) DegreeTwoThreeSpectrum2777.graph fusedMap2168swap=true := by decide +kernel
theorem certified2168swap : Certified (graph core2168) (root 8) 4 0 :=
  of_native_maps core2168 DegreeTwoThreeSpectrum2775.graph DegreeTwoThreeSpectrum2777.graph
    sourceMap2168swap fusedMap2168swap sourceMap2168swap_checked fusedMap2168swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2168
#print axioms sourceMap2168swap_checked
#print axioms fusedMap2168swap_checked
#print axioms certified2168swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
