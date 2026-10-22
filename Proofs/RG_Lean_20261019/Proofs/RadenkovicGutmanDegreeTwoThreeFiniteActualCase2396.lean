/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2396 : Family 9 := level9.get ⟨530,by decide⟩
def sourceMap2396 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2396 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2396_checked : acceptsGraphIso
    (source (graph core2396) (root 9) 0 4) DegreeTwoThreeSpectrum4634.graph sourceMap2396=true := by decide +kernel
theorem fusedMap2396_checked : acceptsGraphIso
    (fused (graph core2396) (root 9) 0 4) DegreeTwoThreeSpectrum4635.graph fusedMap2396=true := by decide +kernel
theorem certified2396 : Certified (graph core2396) (root 9) 0 4 :=
  of_native_maps core2396 DegreeTwoThreeSpectrum4634.graph DegreeTwoThreeSpectrum4635.graph
    sourceMap2396 fusedMap2396 sourceMap2396_checked fusedMap2396_checked
    DegreeTwoThreeFiniteComparisons.comparison2396
#print axioms sourceMap2396_checked
#print axioms fusedMap2396_checked
#print axioms certified2396
def sourceMap2396swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2396swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2396swap_checked : acceptsGraphIso
    (source (graph core2396) (root 9) 4 0) DegreeTwoThreeSpectrum4634.graph sourceMap2396swap=true := by decide +kernel
theorem fusedMap2396swap_checked : acceptsGraphIso
    (fused (graph core2396) (root 9) 4 0) DegreeTwoThreeSpectrum4635.graph fusedMap2396swap=true := by decide +kernel
theorem certified2396swap : Certified (graph core2396) (root 9) 4 0 :=
  of_native_maps core2396 DegreeTwoThreeSpectrum4634.graph DegreeTwoThreeSpectrum4635.graph
    sourceMap2396swap fusedMap2396swap sourceMap2396swap_checked fusedMap2396swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2396
#print axioms sourceMap2396swap_checked
#print axioms fusedMap2396swap_checked
#print axioms certified2396swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
