/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2830 : Family 10 := level10.get ⟨1155,by decide⟩
def sourceMap2830 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2830 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2830_checked : acceptsGraphIso
    (source (graph core2830) (root 10) 0 4) DegreeTwoThreeSpectrum6295.graph sourceMap2830=true := by decide +kernel
theorem fusedMap2830_checked : acceptsGraphIso
    (fused (graph core2830) (root 10) 0 4) DegreeTwoThreeSpectrum6296.graph fusedMap2830=true := by decide +kernel
theorem certified2830 : Certified (graph core2830) (root 10) 0 4 :=
  of_native_maps core2830 DegreeTwoThreeSpectrum6295.graph DegreeTwoThreeSpectrum6296.graph
    sourceMap2830 fusedMap2830 sourceMap2830_checked fusedMap2830_checked
    DegreeTwoThreeFiniteComparisons.comparison2830
#print axioms sourceMap2830_checked
#print axioms fusedMap2830_checked
#print axioms certified2830
def sourceMap2830swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2830swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2830swap_checked : acceptsGraphIso
    (source (graph core2830) (root 10) 4 0) DegreeTwoThreeSpectrum6295.graph sourceMap2830swap=true := by decide +kernel
theorem fusedMap2830swap_checked : acceptsGraphIso
    (fused (graph core2830) (root 10) 4 0) DegreeTwoThreeSpectrum6296.graph fusedMap2830swap=true := by decide +kernel
theorem certified2830swap : Certified (graph core2830) (root 10) 4 0 :=
  of_native_maps core2830 DegreeTwoThreeSpectrum6295.graph DegreeTwoThreeSpectrum6296.graph
    sourceMap2830swap fusedMap2830swap sourceMap2830swap_checked fusedMap2830swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2830
#print axioms sourceMap2830swap_checked
#print axioms fusedMap2830swap_checked
#print axioms certified2830swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
