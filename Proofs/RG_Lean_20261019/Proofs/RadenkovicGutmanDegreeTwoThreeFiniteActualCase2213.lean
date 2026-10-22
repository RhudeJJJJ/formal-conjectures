/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2213 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap2213 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2213 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2213_checked : acceptsGraphIso
    (source (graph core2213) (root 8) 0 4) DegreeTwoThreeSpectrum3020.graph sourceMap2213=true := by decide +kernel
theorem fusedMap2213_checked : acceptsGraphIso
    (fused (graph core2213) (root 8) 0 4) DegreeTwoThreeSpectrum3022.graph fusedMap2213=true := by decide +kernel
theorem certified2213 : Certified (graph core2213) (root 8) 0 4 :=
  of_native_maps core2213 DegreeTwoThreeSpectrum3020.graph DegreeTwoThreeSpectrum3022.graph
    sourceMap2213 fusedMap2213 sourceMap2213_checked fusedMap2213_checked
    DegreeTwoThreeFiniteComparisons.comparison2213
#print axioms sourceMap2213_checked
#print axioms fusedMap2213_checked
#print axioms certified2213
def sourceMap2213swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2213swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2213swap_checked : acceptsGraphIso
    (source (graph core2213) (root 8) 4 0) DegreeTwoThreeSpectrum3020.graph sourceMap2213swap=true := by decide +kernel
theorem fusedMap2213swap_checked : acceptsGraphIso
    (fused (graph core2213) (root 8) 4 0) DegreeTwoThreeSpectrum3022.graph fusedMap2213swap=true := by decide +kernel
theorem certified2213swap : Certified (graph core2213) (root 8) 4 0 :=
  of_native_maps core2213 DegreeTwoThreeSpectrum3020.graph DegreeTwoThreeSpectrum3022.graph
    sourceMap2213swap fusedMap2213swap sourceMap2213swap_checked fusedMap2213swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2213
#print axioms sourceMap2213swap_checked
#print axioms fusedMap2213swap_checked
#print axioms certified2213swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
