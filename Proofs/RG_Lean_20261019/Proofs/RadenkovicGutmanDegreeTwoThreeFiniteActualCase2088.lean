/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2088 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap2088 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2088 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2088_checked : acceptsGraphIso
    (source (graph core2088) (root 7) 0 4) DegreeTwoThreeSpectrum1751.graph sourceMap2088=true := by decide +kernel
theorem fusedMap2088_checked : acceptsGraphIso
    (fused (graph core2088) (root 7) 0 4) DegreeTwoThreeSpectrum1753.graph fusedMap2088=true := by decide +kernel
theorem certified2088 : Certified (graph core2088) (root 7) 0 4 :=
  of_native_maps core2088 DegreeTwoThreeSpectrum1751.graph DegreeTwoThreeSpectrum1753.graph
    sourceMap2088 fusedMap2088 sourceMap2088_checked fusedMap2088_checked
    DegreeTwoThreeFiniteComparisons.comparison2088
#print axioms sourceMap2088_checked
#print axioms fusedMap2088_checked
#print axioms certified2088
def sourceMap2088swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2088swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2088swap_checked : acceptsGraphIso
    (source (graph core2088) (root 7) 4 0) DegreeTwoThreeSpectrum1751.graph sourceMap2088swap=true := by decide +kernel
theorem fusedMap2088swap_checked : acceptsGraphIso
    (fused (graph core2088) (root 7) 4 0) DegreeTwoThreeSpectrum1753.graph fusedMap2088swap=true := by decide +kernel
theorem certified2088swap : Certified (graph core2088) (root 7) 4 0 :=
  of_native_maps core2088 DegreeTwoThreeSpectrum1751.graph DegreeTwoThreeSpectrum1753.graph
    sourceMap2088swap fusedMap2088swap sourceMap2088swap_checked fusedMap2088swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2088
#print axioms sourceMap2088swap_checked
#print axioms fusedMap2088swap_checked
#print axioms certified2088swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
