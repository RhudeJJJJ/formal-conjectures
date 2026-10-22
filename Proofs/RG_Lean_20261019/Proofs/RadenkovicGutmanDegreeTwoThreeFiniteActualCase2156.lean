/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2156 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap2156 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2156 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2156_checked : acceptsGraphIso
    (source (graph core2156) (root 8) 0 4) DegreeTwoThreeSpectrum2603.graph sourceMap2156=true := by decide +kernel
theorem fusedMap2156_checked : acceptsGraphIso
    (fused (graph core2156) (root 8) 0 4) DegreeTwoThreeSpectrum2605.graph fusedMap2156=true := by decide +kernel
theorem certified2156 : Certified (graph core2156) (root 8) 0 4 :=
  of_native_maps core2156 DegreeTwoThreeSpectrum2603.graph DegreeTwoThreeSpectrum2605.graph
    sourceMap2156 fusedMap2156 sourceMap2156_checked fusedMap2156_checked
    DegreeTwoThreeFiniteComparisons.comparison2156
#print axioms sourceMap2156_checked
#print axioms fusedMap2156_checked
#print axioms certified2156
def sourceMap2156swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2156swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2156swap_checked : acceptsGraphIso
    (source (graph core2156) (root 8) 4 0) DegreeTwoThreeSpectrum2603.graph sourceMap2156swap=true := by decide +kernel
theorem fusedMap2156swap_checked : acceptsGraphIso
    (fused (graph core2156) (root 8) 4 0) DegreeTwoThreeSpectrum2605.graph fusedMap2156swap=true := by decide +kernel
theorem certified2156swap : Certified (graph core2156) (root 8) 4 0 :=
  of_native_maps core2156 DegreeTwoThreeSpectrum2603.graph DegreeTwoThreeSpectrum2605.graph
    sourceMap2156swap fusedMap2156swap sourceMap2156swap_checked fusedMap2156swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2156
#print axioms sourceMap2156swap_checked
#print axioms fusedMap2156swap_checked
#print axioms certified2156swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
