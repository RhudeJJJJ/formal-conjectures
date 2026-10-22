/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2945 : Family 10 := level10.get ⟨1427,by decide⟩
def sourceMap2945 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2945 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2945_checked : acceptsGraphIso
    (source (graph core2945) (root 10) 0 4) DegreeTwoThreeSpectrum6881.graph sourceMap2945=true := by decide +kernel
theorem fusedMap2945_checked : acceptsGraphIso
    (fused (graph core2945) (root 10) 0 4) DegreeTwoThreeSpectrum6882.graph fusedMap2945=true := by decide +kernel
theorem certified2945 : Certified (graph core2945) (root 10) 0 4 :=
  of_native_maps core2945 DegreeTwoThreeSpectrum6881.graph DegreeTwoThreeSpectrum6882.graph
    sourceMap2945 fusedMap2945 sourceMap2945_checked fusedMap2945_checked
    DegreeTwoThreeFiniteComparisons.comparison2945
#print axioms sourceMap2945_checked
#print axioms fusedMap2945_checked
#print axioms certified2945
def sourceMap2945swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2945swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2945swap_checked : acceptsGraphIso
    (source (graph core2945) (root 10) 4 0) DegreeTwoThreeSpectrum6881.graph sourceMap2945swap=true := by decide +kernel
theorem fusedMap2945swap_checked : acceptsGraphIso
    (fused (graph core2945) (root 10) 4 0) DegreeTwoThreeSpectrum6882.graph fusedMap2945swap=true := by decide +kernel
theorem certified2945swap : Certified (graph core2945) (root 10) 4 0 :=
  of_native_maps core2945 DegreeTwoThreeSpectrum6881.graph DegreeTwoThreeSpectrum6882.graph
    sourceMap2945swap fusedMap2945swap sourceMap2945swap_checked fusedMap2945swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2945
#print axioms sourceMap2945swap_checked
#print axioms fusedMap2945swap_checked
#print axioms certified2945swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
