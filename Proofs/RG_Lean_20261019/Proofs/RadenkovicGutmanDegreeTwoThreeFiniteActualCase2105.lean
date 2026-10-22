/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2105 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap2105 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2105 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2105_checked : acceptsGraphIso
    (source (graph core2105) (root 7) 0 4) DegreeTwoThreeSpectrum2013.graph sourceMap2105=true := by decide +kernel
theorem fusedMap2105_checked : acceptsGraphIso
    (fused (graph core2105) (root 7) 0 4) DegreeTwoThreeSpectrum1762.graph fusedMap2105=true := by decide +kernel
theorem certified2105 : Certified (graph core2105) (root 7) 0 4 :=
  of_native_maps core2105 DegreeTwoThreeSpectrum2013.graph DegreeTwoThreeSpectrum1762.graph
    sourceMap2105 fusedMap2105 sourceMap2105_checked fusedMap2105_checked
    DegreeTwoThreeFiniteComparisons.comparison2105
#print axioms sourceMap2105_checked
#print axioms fusedMap2105_checked
#print axioms certified2105
def sourceMap2105swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2105swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2105swap_checked : acceptsGraphIso
    (source (graph core2105) (root 7) 4 0) DegreeTwoThreeSpectrum2013.graph sourceMap2105swap=true := by decide +kernel
theorem fusedMap2105swap_checked : acceptsGraphIso
    (fused (graph core2105) (root 7) 4 0) DegreeTwoThreeSpectrum1762.graph fusedMap2105swap=true := by decide +kernel
theorem certified2105swap : Certified (graph core2105) (root 7) 4 0 :=
  of_native_maps core2105 DegreeTwoThreeSpectrum2013.graph DegreeTwoThreeSpectrum1762.graph
    sourceMap2105swap fusedMap2105swap sourceMap2105swap_checked fusedMap2105swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2105
#print axioms sourceMap2105swap_checked
#print axioms fusedMap2105swap_checked
#print axioms certified2105swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
