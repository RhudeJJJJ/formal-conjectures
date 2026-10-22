/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2098 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap2098 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2098 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2098_checked : acceptsGraphIso
    (source (graph core2098) (root 7) 0 4) DegreeTwoThreeSpectrum1890.graph sourceMap2098=true := by decide +kernel
theorem fusedMap2098_checked : acceptsGraphIso
    (fused (graph core2098) (root 7) 0 4) DegreeTwoThreeSpectrum1892.graph fusedMap2098=true := by decide +kernel
theorem certified2098 : Certified (graph core2098) (root 7) 0 4 :=
  of_native_maps core2098 DegreeTwoThreeSpectrum1890.graph DegreeTwoThreeSpectrum1892.graph
    sourceMap2098 fusedMap2098 sourceMap2098_checked fusedMap2098_checked
    DegreeTwoThreeFiniteComparisons.comparison2098
#print axioms sourceMap2098_checked
#print axioms fusedMap2098_checked
#print axioms certified2098
def sourceMap2098swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2098swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2098swap_checked : acceptsGraphIso
    (source (graph core2098) (root 7) 4 0) DegreeTwoThreeSpectrum1890.graph sourceMap2098swap=true := by decide +kernel
theorem fusedMap2098swap_checked : acceptsGraphIso
    (fused (graph core2098) (root 7) 4 0) DegreeTwoThreeSpectrum1892.graph fusedMap2098swap=true := by decide +kernel
theorem certified2098swap : Certified (graph core2098) (root 7) 4 0 :=
  of_native_maps core2098 DegreeTwoThreeSpectrum1890.graph DegreeTwoThreeSpectrum1892.graph
    sourceMap2098swap fusedMap2098swap sourceMap2098swap_checked fusedMap2098swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2098
#print axioms sourceMap2098swap_checked
#print axioms fusedMap2098swap_checked
#print axioms certified2098swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
