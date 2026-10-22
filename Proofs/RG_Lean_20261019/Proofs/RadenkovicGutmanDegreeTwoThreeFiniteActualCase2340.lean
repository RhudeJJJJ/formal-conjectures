/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2340 : Family 9 := level9.get ⟨400,by decide⟩
def sourceMap2340 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2340 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2340_checked : acceptsGraphIso
    (source (graph core2340) (root 9) 0 4) DegreeTwoThreeSpectrum4355.graph sourceMap2340=true := by decide +kernel
theorem fusedMap2340_checked : acceptsGraphIso
    (fused (graph core2340) (root 9) 0 4) DegreeTwoThreeSpectrum4356.graph fusedMap2340=true := by decide +kernel
theorem certified2340 : Certified (graph core2340) (root 9) 0 4 :=
  of_native_maps core2340 DegreeTwoThreeSpectrum4355.graph DegreeTwoThreeSpectrum4356.graph
    sourceMap2340 fusedMap2340 sourceMap2340_checked fusedMap2340_checked
    DegreeTwoThreeFiniteComparisons.comparison2340
#print axioms sourceMap2340_checked
#print axioms fusedMap2340_checked
#print axioms certified2340
def sourceMap2340swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2340swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2340swap_checked : acceptsGraphIso
    (source (graph core2340) (root 9) 4 0) DegreeTwoThreeSpectrum4355.graph sourceMap2340swap=true := by decide +kernel
theorem fusedMap2340swap_checked : acceptsGraphIso
    (fused (graph core2340) (root 9) 4 0) DegreeTwoThreeSpectrum4356.graph fusedMap2340swap=true := by decide +kernel
theorem certified2340swap : Certified (graph core2340) (root 9) 4 0 :=
  of_native_maps core2340 DegreeTwoThreeSpectrum4355.graph DegreeTwoThreeSpectrum4356.graph
    sourceMap2340swap fusedMap2340swap sourceMap2340swap_checked fusedMap2340swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2340
#print axioms sourceMap2340swap_checked
#print axioms fusedMap2340swap_checked
#print axioms certified2340swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
