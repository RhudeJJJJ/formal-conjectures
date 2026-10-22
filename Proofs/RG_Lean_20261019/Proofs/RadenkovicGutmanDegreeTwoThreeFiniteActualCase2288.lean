/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2288 : Family 9 := level9.get ⟨264,by decide⟩
def sourceMap2288 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2288 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2288_checked : acceptsGraphIso
    (source (graph core2288) (root 9) 0 4) DegreeTwoThreeSpectrum4591.graph sourceMap2288=true := by decide +kernel
theorem fusedMap2288_checked : acceptsGraphIso
    (fused (graph core2288) (root 9) 0 4) DegreeTwoThreeSpectrum4074.graph fusedMap2288=true := by decide +kernel
theorem certified2288 : Certified (graph core2288) (root 9) 0 4 :=
  of_native_maps core2288 DegreeTwoThreeSpectrum4591.graph DegreeTwoThreeSpectrum4074.graph
    sourceMap2288 fusedMap2288 sourceMap2288_checked fusedMap2288_checked
    DegreeTwoThreeFiniteComparisons.comparison2288
#print axioms sourceMap2288_checked
#print axioms fusedMap2288_checked
#print axioms certified2288
def sourceMap2288swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2288swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2288swap_checked : acceptsGraphIso
    (source (graph core2288) (root 9) 4 0) DegreeTwoThreeSpectrum4591.graph sourceMap2288swap=true := by decide +kernel
theorem fusedMap2288swap_checked : acceptsGraphIso
    (fused (graph core2288) (root 9) 4 0) DegreeTwoThreeSpectrum4074.graph fusedMap2288swap=true := by decide +kernel
theorem certified2288swap : Certified (graph core2288) (root 9) 4 0 :=
  of_native_maps core2288 DegreeTwoThreeSpectrum4591.graph DegreeTwoThreeSpectrum4074.graph
    sourceMap2288swap fusedMap2288swap sourceMap2288swap_checked fusedMap2288swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2288
#print axioms sourceMap2288swap_checked
#print axioms fusedMap2288swap_checked
#print axioms certified2288swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
