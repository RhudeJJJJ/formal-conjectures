/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2818 : Family 10 := level10.get ⟨1122,by decide⟩
def sourceMap2818 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2818 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2818_checked : acceptsGraphIso
    (source (graph core2818) (root 10) 0 4) DegreeTwoThreeSpectrum6229.graph sourceMap2818=true := by decide +kernel
theorem fusedMap2818_checked : acceptsGraphIso
    (fused (graph core2818) (root 10) 0 4) DegreeTwoThreeSpectrum6230.graph fusedMap2818=true := by decide +kernel
theorem certified2818 : Certified (graph core2818) (root 10) 0 4 :=
  of_native_maps core2818 DegreeTwoThreeSpectrum6229.graph DegreeTwoThreeSpectrum6230.graph
    sourceMap2818 fusedMap2818 sourceMap2818_checked fusedMap2818_checked
    DegreeTwoThreeFiniteComparisons.comparison2818
#print axioms sourceMap2818_checked
#print axioms fusedMap2818_checked
#print axioms certified2818
def sourceMap2818swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2818swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2818swap_checked : acceptsGraphIso
    (source (graph core2818) (root 10) 4 0) DegreeTwoThreeSpectrum6229.graph sourceMap2818swap=true := by decide +kernel
theorem fusedMap2818swap_checked : acceptsGraphIso
    (fused (graph core2818) (root 10) 4 0) DegreeTwoThreeSpectrum6230.graph fusedMap2818swap=true := by decide +kernel
theorem certified2818swap : Certified (graph core2818) (root 10) 4 0 :=
  of_native_maps core2818 DegreeTwoThreeSpectrum6229.graph DegreeTwoThreeSpectrum6230.graph
    sourceMap2818swap fusedMap2818swap sourceMap2818swap_checked fusedMap2818swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2818
#print axioms sourceMap2818swap_checked
#print axioms fusedMap2818swap_checked
#print axioms certified2818swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
