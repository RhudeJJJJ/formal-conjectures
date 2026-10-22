/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2430 : Family 9 := level9.get ⟨611,by decide⟩
def sourceMap2430 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2430 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2430_checked : acceptsGraphIso
    (source (graph core2430) (root 9) 0 4) DegreeTwoThreeSpectrum4748.graph sourceMap2430=true := by decide +kernel
theorem fusedMap2430_checked : acceptsGraphIso
    (fused (graph core2430) (root 9) 0 4) DegreeTwoThreeSpectrum4307.graph fusedMap2430=true := by decide +kernel
theorem certified2430 : Certified (graph core2430) (root 9) 0 4 :=
  of_native_maps core2430 DegreeTwoThreeSpectrum4748.graph DegreeTwoThreeSpectrum4307.graph
    sourceMap2430 fusedMap2430 sourceMap2430_checked fusedMap2430_checked
    DegreeTwoThreeFiniteComparisons.comparison2430
#print axioms sourceMap2430_checked
#print axioms fusedMap2430_checked
#print axioms certified2430
def sourceMap2430swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2430swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2430swap_checked : acceptsGraphIso
    (source (graph core2430) (root 9) 4 0) DegreeTwoThreeSpectrum4748.graph sourceMap2430swap=true := by decide +kernel
theorem fusedMap2430swap_checked : acceptsGraphIso
    (fused (graph core2430) (root 9) 4 0) DegreeTwoThreeSpectrum4307.graph fusedMap2430swap=true := by decide +kernel
theorem certified2430swap : Certified (graph core2430) (root 9) 4 0 :=
  of_native_maps core2430 DegreeTwoThreeSpectrum4748.graph DegreeTwoThreeSpectrum4307.graph
    sourceMap2430swap fusedMap2430swap sourceMap2430swap_checked fusedMap2430swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2430
#print axioms sourceMap2430swap_checked
#print axioms fusedMap2430swap_checked
#print axioms certified2430swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
