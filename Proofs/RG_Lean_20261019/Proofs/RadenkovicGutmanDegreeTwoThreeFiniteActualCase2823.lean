/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2823 : Family 10 := level10.get ⟨1137,by decide⟩
def sourceMap2823 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2823 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2823_checked : acceptsGraphIso
    (source (graph core2823) (root 10) 0 4) DegreeTwoThreeSpectrum6262.graph sourceMap2823=true := by decide +kernel
theorem fusedMap2823_checked : acceptsGraphIso
    (fused (graph core2823) (root 10) 0 4) DegreeTwoThreeSpectrum6263.graph fusedMap2823=true := by decide +kernel
theorem certified2823 : Certified (graph core2823) (root 10) 0 4 :=
  of_native_maps core2823 DegreeTwoThreeSpectrum6262.graph DegreeTwoThreeSpectrum6263.graph
    sourceMap2823 fusedMap2823 sourceMap2823_checked fusedMap2823_checked
    DegreeTwoThreeFiniteComparisons.comparison2823
#print axioms sourceMap2823_checked
#print axioms fusedMap2823_checked
#print axioms certified2823
def sourceMap2823swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2823swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2823swap_checked : acceptsGraphIso
    (source (graph core2823) (root 10) 4 0) DegreeTwoThreeSpectrum6262.graph sourceMap2823swap=true := by decide +kernel
theorem fusedMap2823swap_checked : acceptsGraphIso
    (fused (graph core2823) (root 10) 4 0) DegreeTwoThreeSpectrum6263.graph fusedMap2823swap=true := by decide +kernel
theorem certified2823swap : Certified (graph core2823) (root 10) 4 0 :=
  of_native_maps core2823 DegreeTwoThreeSpectrum6262.graph DegreeTwoThreeSpectrum6263.graph
    sourceMap2823swap fusedMap2823swap sourceMap2823swap_checked fusedMap2823swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2823
#print axioms sourceMap2823swap_checked
#print axioms fusedMap2823swap_checked
#print axioms certified2823swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
