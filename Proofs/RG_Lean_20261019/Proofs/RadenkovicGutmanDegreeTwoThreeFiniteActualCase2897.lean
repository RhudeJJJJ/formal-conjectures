/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2897 : Family 10 := level10.get ⟨1313,by decide⟩
def sourceMap2897 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2897 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2897_checked : acceptsGraphIso
    (source (graph core2897) (root 10) 0 4) DegreeTwoThreeSpectrum6612.graph sourceMap2897=true := by decide +kernel
theorem fusedMap2897_checked : acceptsGraphIso
    (fused (graph core2897) (root 10) 0 4) DegreeTwoThreeSpectrum6613.graph fusedMap2897=true := by decide +kernel
theorem certified2897 : Certified (graph core2897) (root 10) 0 4 :=
  of_native_maps core2897 DegreeTwoThreeSpectrum6612.graph DegreeTwoThreeSpectrum6613.graph
    sourceMap2897 fusedMap2897 sourceMap2897_checked fusedMap2897_checked
    DegreeTwoThreeFiniteComparisons.comparison2897
#print axioms sourceMap2897_checked
#print axioms fusedMap2897_checked
#print axioms certified2897
def sourceMap2897swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2897swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2897swap_checked : acceptsGraphIso
    (source (graph core2897) (root 10) 4 0) DegreeTwoThreeSpectrum6612.graph sourceMap2897swap=true := by decide +kernel
theorem fusedMap2897swap_checked : acceptsGraphIso
    (fused (graph core2897) (root 10) 4 0) DegreeTwoThreeSpectrum6613.graph fusedMap2897swap=true := by decide +kernel
theorem certified2897swap : Certified (graph core2897) (root 10) 4 0 :=
  of_native_maps core2897 DegreeTwoThreeSpectrum6612.graph DegreeTwoThreeSpectrum6613.graph
    sourceMap2897swap fusedMap2897swap sourceMap2897swap_checked fusedMap2897swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2897
#print axioms sourceMap2897swap_checked
#print axioms fusedMap2897swap_checked
#print axioms certified2897swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
