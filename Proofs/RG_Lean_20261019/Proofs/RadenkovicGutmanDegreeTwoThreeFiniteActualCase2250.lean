/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2250 : Family 9 := level9.get ⟨146,by decide⟩
def sourceMap2250 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2250 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2250_checked : acceptsGraphIso
    (source (graph core2250) (root 9) 0 4) DegreeTwoThreeSpectrum4232.graph sourceMap2250=true := by decide +kernel
theorem fusedMap2250_checked : acceptsGraphIso
    (fused (graph core2250) (root 9) 0 4) DegreeTwoThreeSpectrum3901.graph fusedMap2250=true := by decide +kernel
theorem certified2250 : Certified (graph core2250) (root 9) 0 4 :=
  of_native_maps core2250 DegreeTwoThreeSpectrum4232.graph DegreeTwoThreeSpectrum3901.graph
    sourceMap2250 fusedMap2250 sourceMap2250_checked fusedMap2250_checked
    DegreeTwoThreeFiniteComparisons.comparison2250
#print axioms sourceMap2250_checked
#print axioms fusedMap2250_checked
#print axioms certified2250
def sourceMap2250swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2250swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2250swap_checked : acceptsGraphIso
    (source (graph core2250) (root 9) 4 0) DegreeTwoThreeSpectrum4232.graph sourceMap2250swap=true := by decide +kernel
theorem fusedMap2250swap_checked : acceptsGraphIso
    (fused (graph core2250) (root 9) 4 0) DegreeTwoThreeSpectrum3901.graph fusedMap2250swap=true := by decide +kernel
theorem certified2250swap : Certified (graph core2250) (root 9) 4 0 :=
  of_native_maps core2250 DegreeTwoThreeSpectrum4232.graph DegreeTwoThreeSpectrum3901.graph
    sourceMap2250swap fusedMap2250swap sourceMap2250swap_checked fusedMap2250swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2250
#print axioms sourceMap2250swap_checked
#print axioms fusedMap2250swap_checked
#print axioms certified2250swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
