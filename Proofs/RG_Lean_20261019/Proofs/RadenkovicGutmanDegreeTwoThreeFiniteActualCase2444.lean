/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2444 : Family 9 := level9.get ⟨653,by decide⟩
def sourceMap2444 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2444 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2444_checked : acceptsGraphIso
    (source (graph core2444) (root 9) 0 4) DegreeTwoThreeSpectrum4817.graph sourceMap2444=true := by decide +kernel
theorem fusedMap2444_checked : acceptsGraphIso
    (fused (graph core2444) (root 9) 0 4) DegreeTwoThreeSpectrum4445.graph fusedMap2444=true := by decide +kernel
theorem certified2444 : Certified (graph core2444) (root 9) 0 4 :=
  of_native_maps core2444 DegreeTwoThreeSpectrum4817.graph DegreeTwoThreeSpectrum4445.graph
    sourceMap2444 fusedMap2444 sourceMap2444_checked fusedMap2444_checked
    DegreeTwoThreeFiniteComparisons.comparison2444
#print axioms sourceMap2444_checked
#print axioms fusedMap2444_checked
#print axioms certified2444
def sourceMap2444swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2444swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2444swap_checked : acceptsGraphIso
    (source (graph core2444) (root 9) 4 0) DegreeTwoThreeSpectrum4817.graph sourceMap2444swap=true := by decide +kernel
theorem fusedMap2444swap_checked : acceptsGraphIso
    (fused (graph core2444) (root 9) 4 0) DegreeTwoThreeSpectrum4445.graph fusedMap2444swap=true := by decide +kernel
theorem certified2444swap : Certified (graph core2444) (root 9) 4 0 :=
  of_native_maps core2444 DegreeTwoThreeSpectrum4817.graph DegreeTwoThreeSpectrum4445.graph
    sourceMap2444swap fusedMap2444swap sourceMap2444swap_checked fusedMap2444swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2444
#print axioms sourceMap2444swap_checked
#print axioms fusedMap2444swap_checked
#print axioms certified2444swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
