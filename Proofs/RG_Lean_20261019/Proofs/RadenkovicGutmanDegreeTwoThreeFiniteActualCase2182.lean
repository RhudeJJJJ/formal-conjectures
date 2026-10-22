/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2182 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap2182 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2182 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2182_checked : acceptsGraphIso
    (source (graph core2182) (root 8) 0 4) DegreeTwoThreeSpectrum3035.graph sourceMap2182=true := by decide +kernel
theorem fusedMap2182_checked : acceptsGraphIso
    (fused (graph core2182) (root 8) 0 4) DegreeTwoThreeSpectrum2442.graph fusedMap2182=true := by decide +kernel
theorem certified2182 : Certified (graph core2182) (root 8) 0 4 :=
  of_native_maps core2182 DegreeTwoThreeSpectrum3035.graph DegreeTwoThreeSpectrum2442.graph
    sourceMap2182 fusedMap2182 sourceMap2182_checked fusedMap2182_checked
    DegreeTwoThreeFiniteComparisons.comparison2182
#print axioms sourceMap2182_checked
#print axioms fusedMap2182_checked
#print axioms certified2182
def sourceMap2182swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2182swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2182swap_checked : acceptsGraphIso
    (source (graph core2182) (root 8) 4 0) DegreeTwoThreeSpectrum3035.graph sourceMap2182swap=true := by decide +kernel
theorem fusedMap2182swap_checked : acceptsGraphIso
    (fused (graph core2182) (root 8) 4 0) DegreeTwoThreeSpectrum2442.graph fusedMap2182swap=true := by decide +kernel
theorem certified2182swap : Certified (graph core2182) (root 8) 4 0 :=
  of_native_maps core2182 DegreeTwoThreeSpectrum3035.graph DegreeTwoThreeSpectrum2442.graph
    sourceMap2182swap fusedMap2182swap sourceMap2182swap_checked fusedMap2182swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2182
#print axioms sourceMap2182swap_checked
#print axioms fusedMap2182swap_checked
#print axioms certified2182swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
