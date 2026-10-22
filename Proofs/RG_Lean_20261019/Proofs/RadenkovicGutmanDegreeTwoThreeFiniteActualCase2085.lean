/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2085 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap2085 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11] (sourceLabel 7 0 4 v)
def fusedMap2085 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2085_checked : acceptsGraphIso
    (source (graph core2085) (root 7) 0 4) DegreeTwoThreeSpectrum1901.graph sourceMap2085=true := by decide +kernel
theorem fusedMap2085_checked : acceptsGraphIso
    (fused (graph core2085) (root 7) 0 4) DegreeTwoThreeSpectrum1726.graph fusedMap2085=true := by decide +kernel
theorem certified2085 : Certified (graph core2085) (root 7) 0 4 :=
  of_native_maps core2085 DegreeTwoThreeSpectrum1901.graph DegreeTwoThreeSpectrum1726.graph
    sourceMap2085 fusedMap2085 sourceMap2085_checked fusedMap2085_checked
    DegreeTwoThreeFiniteComparisons.comparison2085
#print axioms sourceMap2085_checked
#print axioms fusedMap2085_checked
#print axioms certified2085
def sourceMap2085swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,12,7,8,9,10,11,13] (sourceLabel 7 4 0 v)
def fusedMap2085swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2085swap_checked : acceptsGraphIso
    (source (graph core2085) (root 7) 4 0) DegreeTwoThreeSpectrum1901.graph sourceMap2085swap=true := by decide +kernel
theorem fusedMap2085swap_checked : acceptsGraphIso
    (fused (graph core2085) (root 7) 4 0) DegreeTwoThreeSpectrum1726.graph fusedMap2085swap=true := by decide +kernel
theorem certified2085swap : Certified (graph core2085) (root 7) 4 0 :=
  of_native_maps core2085 DegreeTwoThreeSpectrum1901.graph DegreeTwoThreeSpectrum1726.graph
    sourceMap2085swap fusedMap2085swap sourceMap2085swap_checked fusedMap2085swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2085
#print axioms sourceMap2085swap_checked
#print axioms fusedMap2085swap_checked
#print axioms certified2085swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
