/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2885 : Family 10 := level10.get ⟨1284,by decide⟩
def sourceMap2885 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2885 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2885_checked : acceptsGraphIso
    (source (graph core2885) (root 10) 0 4) DegreeTwoThreeSpectrum6552.graph sourceMap2885=true := by decide +kernel
theorem fusedMap2885_checked : acceptsGraphIso
    (fused (graph core2885) (root 10) 0 4) DegreeTwoThreeSpectrum6553.graph fusedMap2885=true := by decide +kernel
theorem certified2885 : Certified (graph core2885) (root 10) 0 4 :=
  of_native_maps core2885 DegreeTwoThreeSpectrum6552.graph DegreeTwoThreeSpectrum6553.graph
    sourceMap2885 fusedMap2885 sourceMap2885_checked fusedMap2885_checked
    DegreeTwoThreeFiniteComparisons.comparison2885
#print axioms sourceMap2885_checked
#print axioms fusedMap2885_checked
#print axioms certified2885
def sourceMap2885swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2885swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2885swap_checked : acceptsGraphIso
    (source (graph core2885) (root 10) 4 0) DegreeTwoThreeSpectrum6552.graph sourceMap2885swap=true := by decide +kernel
theorem fusedMap2885swap_checked : acceptsGraphIso
    (fused (graph core2885) (root 10) 4 0) DegreeTwoThreeSpectrum6553.graph fusedMap2885swap=true := by decide +kernel
theorem certified2885swap : Certified (graph core2885) (root 10) 4 0 :=
  of_native_maps core2885 DegreeTwoThreeSpectrum6552.graph DegreeTwoThreeSpectrum6553.graph
    sourceMap2885swap fusedMap2885swap sourceMap2885swap_checked fusedMap2885swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2885
#print axioms sourceMap2885swap_checked
#print axioms fusedMap2885swap_checked
#print axioms certified2885swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
