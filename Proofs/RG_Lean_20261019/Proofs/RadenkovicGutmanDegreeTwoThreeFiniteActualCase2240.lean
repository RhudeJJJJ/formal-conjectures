/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2240 : Family 9 := level9.get ⟨116,by decide⟩
def sourceMap2240 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2240 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2240_checked : acceptsGraphIso
    (source (graph core2240) (root 9) 0 4) DegreeTwoThreeSpectrum4131.graph sourceMap2240=true := by decide +kernel
theorem fusedMap2240_checked : acceptsGraphIso
    (fused (graph core2240) (root 9) 0 4) DegreeTwoThreeSpectrum4132.graph fusedMap2240=true := by decide +kernel
theorem certified2240 : Certified (graph core2240) (root 9) 0 4 :=
  of_native_maps core2240 DegreeTwoThreeSpectrum4131.graph DegreeTwoThreeSpectrum4132.graph
    sourceMap2240 fusedMap2240 sourceMap2240_checked fusedMap2240_checked
    DegreeTwoThreeFiniteComparisons.comparison2240
#print axioms sourceMap2240_checked
#print axioms fusedMap2240_checked
#print axioms certified2240
def sourceMap2240swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2240swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2240swap_checked : acceptsGraphIso
    (source (graph core2240) (root 9) 4 0) DegreeTwoThreeSpectrum4131.graph sourceMap2240swap=true := by decide +kernel
theorem fusedMap2240swap_checked : acceptsGraphIso
    (fused (graph core2240) (root 9) 4 0) DegreeTwoThreeSpectrum4132.graph fusedMap2240swap=true := by decide +kernel
theorem certified2240swap : Certified (graph core2240) (root 9) 4 0 :=
  of_native_maps core2240 DegreeTwoThreeSpectrum4131.graph DegreeTwoThreeSpectrum4132.graph
    sourceMap2240swap fusedMap2240swap sourceMap2240swap_checked fusedMap2240swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2240
#print axioms sourceMap2240swap_checked
#print axioms fusedMap2240swap_checked
#print axioms certified2240swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
