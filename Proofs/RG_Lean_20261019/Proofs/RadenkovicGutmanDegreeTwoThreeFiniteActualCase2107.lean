/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2107 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap2107 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2107 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2107_checked : acceptsGraphIso
    (source (graph core2107) (root 7) 0 4) DegreeTwoThreeSpectrum2042.graph sourceMap2107=true := by decide +kernel
theorem fusedMap2107_checked : acceptsGraphIso
    (fused (graph core2107) (root 7) 0 4) DegreeTwoThreeSpectrum1775.graph fusedMap2107=true := by decide +kernel
theorem certified2107 : Certified (graph core2107) (root 7) 0 4 :=
  of_native_maps core2107 DegreeTwoThreeSpectrum2042.graph DegreeTwoThreeSpectrum1775.graph
    sourceMap2107 fusedMap2107 sourceMap2107_checked fusedMap2107_checked
    DegreeTwoThreeFiniteComparisons.comparison2107
#print axioms sourceMap2107_checked
#print axioms fusedMap2107_checked
#print axioms certified2107
def sourceMap2107swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2107swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2107swap_checked : acceptsGraphIso
    (source (graph core2107) (root 7) 4 0) DegreeTwoThreeSpectrum2042.graph sourceMap2107swap=true := by decide +kernel
theorem fusedMap2107swap_checked : acceptsGraphIso
    (fused (graph core2107) (root 7) 4 0) DegreeTwoThreeSpectrum1775.graph fusedMap2107swap=true := by decide +kernel
theorem certified2107swap : Certified (graph core2107) (root 7) 4 0 :=
  of_native_maps core2107 DegreeTwoThreeSpectrum2042.graph DegreeTwoThreeSpectrum1775.graph
    sourceMap2107swap fusedMap2107swap sourceMap2107swap_checked fusedMap2107swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2107
#print axioms sourceMap2107swap_checked
#print axioms fusedMap2107swap_checked
#print axioms certified2107swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
