/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2282 : Family 9 := level9.get ⟨245,by decide⟩
def sourceMap2282 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2282 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2282_checked : acceptsGraphIso
    (source (graph core2282) (root 9) 0 4) DegreeTwoThreeSpectrum4532.graph sourceMap2282=true := by decide +kernel
theorem fusedMap2282_checked : acceptsGraphIso
    (fused (graph core2282) (root 9) 0 4) DegreeTwoThreeSpectrum4043.graph fusedMap2282=true := by decide +kernel
theorem certified2282 : Certified (graph core2282) (root 9) 0 4 :=
  of_native_maps core2282 DegreeTwoThreeSpectrum4532.graph DegreeTwoThreeSpectrum4043.graph
    sourceMap2282 fusedMap2282 sourceMap2282_checked fusedMap2282_checked
    DegreeTwoThreeFiniteComparisons.comparison2282
#print axioms sourceMap2282_checked
#print axioms fusedMap2282_checked
#print axioms certified2282
def sourceMap2282swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2282swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2282swap_checked : acceptsGraphIso
    (source (graph core2282) (root 9) 4 0) DegreeTwoThreeSpectrum4532.graph sourceMap2282swap=true := by decide +kernel
theorem fusedMap2282swap_checked : acceptsGraphIso
    (fused (graph core2282) (root 9) 4 0) DegreeTwoThreeSpectrum4043.graph fusedMap2282swap=true := by decide +kernel
theorem certified2282swap : Certified (graph core2282) (root 9) 4 0 :=
  of_native_maps core2282 DegreeTwoThreeSpectrum4532.graph DegreeTwoThreeSpectrum4043.graph
    sourceMap2282swap fusedMap2282swap sourceMap2282swap_checked fusedMap2282swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2282
#print axioms sourceMap2282swap_checked
#print axioms fusedMap2282swap_checked
#print axioms certified2282swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
