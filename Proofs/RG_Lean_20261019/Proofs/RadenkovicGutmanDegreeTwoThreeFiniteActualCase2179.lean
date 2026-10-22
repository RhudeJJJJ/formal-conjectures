/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2179 : Family 8 := level8.get ⟨181,by decide⟩
def sourceMap2179 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2179 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2179_checked : acceptsGraphIso
    (source (graph core2179) (root 8) 0 4) DegreeTwoThreeSpectrum2951.graph sourceMap2179=true := by decide +kernel
theorem fusedMap2179_checked : acceptsGraphIso
    (fused (graph core2179) (root 8) 0 4) DegreeTwoThreeSpectrum2953.graph fusedMap2179=true := by decide +kernel
theorem certified2179 : Certified (graph core2179) (root 8) 0 4 :=
  of_native_maps core2179 DegreeTwoThreeSpectrum2951.graph DegreeTwoThreeSpectrum2953.graph
    sourceMap2179 fusedMap2179 sourceMap2179_checked fusedMap2179_checked
    DegreeTwoThreeFiniteComparisons.comparison2179
#print axioms sourceMap2179_checked
#print axioms fusedMap2179_checked
#print axioms certified2179
def sourceMap2179swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2179swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2179swap_checked : acceptsGraphIso
    (source (graph core2179) (root 8) 4 0) DegreeTwoThreeSpectrum2951.graph sourceMap2179swap=true := by decide +kernel
theorem fusedMap2179swap_checked : acceptsGraphIso
    (fused (graph core2179) (root 8) 4 0) DegreeTwoThreeSpectrum2953.graph fusedMap2179swap=true := by decide +kernel
theorem certified2179swap : Certified (graph core2179) (root 8) 4 0 :=
  of_native_maps core2179 DegreeTwoThreeSpectrum2951.graph DegreeTwoThreeSpectrum2953.graph
    sourceMap2179swap fusedMap2179swap sourceMap2179swap_checked fusedMap2179swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2179
#print axioms sourceMap2179swap_checked
#print axioms fusedMap2179swap_checked
#print axioms certified2179swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
