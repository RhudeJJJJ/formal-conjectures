/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2101 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap2101 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2101 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2101_checked : acceptsGraphIso
    (source (graph core2101) (root 7) 0 4) DegreeTwoThreeSpectrum1942.graph sourceMap2101=true := by decide +kernel
theorem fusedMap2101_checked : acceptsGraphIso
    (fused (graph core2101) (root 7) 0 4) DegreeTwoThreeSpectrum1740.graph fusedMap2101=true := by decide +kernel
theorem certified2101 : Certified (graph core2101) (root 7) 0 4 :=
  of_native_maps core2101 DegreeTwoThreeSpectrum1942.graph DegreeTwoThreeSpectrum1740.graph
    sourceMap2101 fusedMap2101 sourceMap2101_checked fusedMap2101_checked
    DegreeTwoThreeFiniteComparisons.comparison2101
#print axioms sourceMap2101_checked
#print axioms fusedMap2101_checked
#print axioms certified2101
def sourceMap2101swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2101swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2101swap_checked : acceptsGraphIso
    (source (graph core2101) (root 7) 4 0) DegreeTwoThreeSpectrum1942.graph sourceMap2101swap=true := by decide +kernel
theorem fusedMap2101swap_checked : acceptsGraphIso
    (fused (graph core2101) (root 7) 4 0) DegreeTwoThreeSpectrum1740.graph fusedMap2101swap=true := by decide +kernel
theorem certified2101swap : Certified (graph core2101) (root 7) 4 0 :=
  of_native_maps core2101 DegreeTwoThreeSpectrum1942.graph DegreeTwoThreeSpectrum1740.graph
    sourceMap2101swap fusedMap2101swap sourceMap2101swap_checked fusedMap2101swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2101
#print axioms sourceMap2101swap_checked
#print axioms fusedMap2101swap_checked
#print axioms certified2101swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
