/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2860 : Family 10 := level10.get ⟨1221,by decide⟩
def sourceMap2860 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2860 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2860_checked : acceptsGraphIso
    (source (graph core2860) (root 10) 0 4) DegreeTwoThreeSpectrum6418.graph sourceMap2860=true := by decide +kernel
theorem fusedMap2860_checked : acceptsGraphIso
    (fused (graph core2860) (root 10) 0 4) DegreeTwoThreeSpectrum6419.graph fusedMap2860=true := by decide +kernel
theorem certified2860 : Certified (graph core2860) (root 10) 0 4 :=
  of_native_maps core2860 DegreeTwoThreeSpectrum6418.graph DegreeTwoThreeSpectrum6419.graph
    sourceMap2860 fusedMap2860 sourceMap2860_checked fusedMap2860_checked
    DegreeTwoThreeFiniteComparisons.comparison2860
#print axioms sourceMap2860_checked
#print axioms fusedMap2860_checked
#print axioms certified2860
def sourceMap2860swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2860swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2860swap_checked : acceptsGraphIso
    (source (graph core2860) (root 10) 4 0) DegreeTwoThreeSpectrum6418.graph sourceMap2860swap=true := by decide +kernel
theorem fusedMap2860swap_checked : acceptsGraphIso
    (fused (graph core2860) (root 10) 4 0) DegreeTwoThreeSpectrum6419.graph fusedMap2860swap=true := by decide +kernel
theorem certified2860swap : Certified (graph core2860) (root 10) 4 0 :=
  of_native_maps core2860 DegreeTwoThreeSpectrum6418.graph DegreeTwoThreeSpectrum6419.graph
    sourceMap2860swap fusedMap2860swap sourceMap2860swap_checked fusedMap2860swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2860
#print axioms sourceMap2860swap_checked
#print axioms fusedMap2860swap_checked
#print axioms certified2860swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
