/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2833 : Family 10 := level10.get ⟨1160,by decide⟩
def sourceMap2833 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2833 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2833_checked : acceptsGraphIso
    (source (graph core2833) (root 10) 0 4) DegreeTwoThreeSpectrum6303.graph sourceMap2833=true := by decide +kernel
theorem fusedMap2833_checked : acceptsGraphIso
    (fused (graph core2833) (root 10) 0 4) DegreeTwoThreeSpectrum6304.graph fusedMap2833=true := by decide +kernel
theorem certified2833 : Certified (graph core2833) (root 10) 0 4 :=
  of_native_maps core2833 DegreeTwoThreeSpectrum6303.graph DegreeTwoThreeSpectrum6304.graph
    sourceMap2833 fusedMap2833 sourceMap2833_checked fusedMap2833_checked
    DegreeTwoThreeFiniteComparisons.comparison2833
#print axioms sourceMap2833_checked
#print axioms fusedMap2833_checked
#print axioms certified2833
def sourceMap2833swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2833swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2833swap_checked : acceptsGraphIso
    (source (graph core2833) (root 10) 4 0) DegreeTwoThreeSpectrum6303.graph sourceMap2833swap=true := by decide +kernel
theorem fusedMap2833swap_checked : acceptsGraphIso
    (fused (graph core2833) (root 10) 4 0) DegreeTwoThreeSpectrum6304.graph fusedMap2833swap=true := by decide +kernel
theorem certified2833swap : Certified (graph core2833) (root 10) 4 0 :=
  of_native_maps core2833 DegreeTwoThreeSpectrum6303.graph DegreeTwoThreeSpectrum6304.graph
    sourceMap2833swap fusedMap2833swap sourceMap2833swap_checked fusedMap2833swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2833
#print axioms sourceMap2833swap_checked
#print axioms fusedMap2833swap_checked
#print axioms certified2833swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
