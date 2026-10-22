/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2190 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap2190 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2190 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2190_checked : acceptsGraphIso
    (source (graph core2190) (root 8) 0 4) DegreeTwoThreeSpectrum3181.graph sourceMap2190=true := by decide +kernel
theorem fusedMap2190_checked : acceptsGraphIso
    (fused (graph core2190) (root 8) 0 4) DegreeTwoThreeSpectrum2507.graph fusedMap2190=true := by decide +kernel
theorem certified2190 : Certified (graph core2190) (root 8) 0 4 :=
  of_native_maps core2190 DegreeTwoThreeSpectrum3181.graph DegreeTwoThreeSpectrum2507.graph
    sourceMap2190 fusedMap2190 sourceMap2190_checked fusedMap2190_checked
    DegreeTwoThreeFiniteComparisons.comparison2190
#print axioms sourceMap2190_checked
#print axioms fusedMap2190_checked
#print axioms certified2190
def sourceMap2190swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2190swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2190swap_checked : acceptsGraphIso
    (source (graph core2190) (root 8) 4 0) DegreeTwoThreeSpectrum3181.graph sourceMap2190swap=true := by decide +kernel
theorem fusedMap2190swap_checked : acceptsGraphIso
    (fused (graph core2190) (root 8) 4 0) DegreeTwoThreeSpectrum2507.graph fusedMap2190swap=true := by decide +kernel
theorem certified2190swap : Certified (graph core2190) (root 8) 4 0 :=
  of_native_maps core2190 DegreeTwoThreeSpectrum3181.graph DegreeTwoThreeSpectrum2507.graph
    sourceMap2190swap fusedMap2190swap sourceMap2190swap_checked fusedMap2190swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2190
#print axioms sourceMap2190swap_checked
#print axioms fusedMap2190swap_checked
#print axioms certified2190swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
