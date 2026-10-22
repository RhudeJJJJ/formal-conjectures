/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2089 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap2089 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2089 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2089_checked : acceptsGraphIso
    (source (graph core2089) (root 7) 0 4) DegreeTwoThreeSpectrum1769.graph sourceMap2089=true := by decide +kernel
theorem fusedMap2089_checked : acceptsGraphIso
    (fused (graph core2089) (root 7) 0 4) DegreeTwoThreeSpectrum1771.graph fusedMap2089=true := by decide +kernel
theorem certified2089 : Certified (graph core2089) (root 7) 0 4 :=
  of_native_maps core2089 DegreeTwoThreeSpectrum1769.graph DegreeTwoThreeSpectrum1771.graph
    sourceMap2089 fusedMap2089 sourceMap2089_checked fusedMap2089_checked
    DegreeTwoThreeFiniteComparisons.comparison2089
#print axioms sourceMap2089_checked
#print axioms fusedMap2089_checked
#print axioms certified2089
def sourceMap2089swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2089swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2089swap_checked : acceptsGraphIso
    (source (graph core2089) (root 7) 4 0) DegreeTwoThreeSpectrum1769.graph sourceMap2089swap=true := by decide +kernel
theorem fusedMap2089swap_checked : acceptsGraphIso
    (fused (graph core2089) (root 7) 4 0) DegreeTwoThreeSpectrum1771.graph fusedMap2089swap=true := by decide +kernel
theorem certified2089swap : Certified (graph core2089) (root 7) 4 0 :=
  of_native_maps core2089 DegreeTwoThreeSpectrum1769.graph DegreeTwoThreeSpectrum1771.graph
    sourceMap2089swap fusedMap2089swap sourceMap2089swap_checked fusedMap2089swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2089
#print axioms sourceMap2089swap_checked
#print axioms fusedMap2089swap_checked
#print axioms certified2089swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
