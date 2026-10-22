/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2681 : Family 10 := level10.get ⟨770,by decide⟩
def sourceMap2681 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2681 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2681_checked : acceptsGraphIso
    (source (graph core2681) (root 10) 0 4) DegreeTwoThreeSpectrum6696.graph sourceMap2681=true := by decide +kernel
theorem fusedMap2681_checked : acceptsGraphIso
    (fused (graph core2681) (root 10) 0 4) DegreeTwoThreeSpectrum5548.graph fusedMap2681=true := by decide +kernel
theorem certified2681 : Certified (graph core2681) (root 10) 0 4 :=
  of_native_maps core2681 DegreeTwoThreeSpectrum6696.graph DegreeTwoThreeSpectrum5548.graph
    sourceMap2681 fusedMap2681 sourceMap2681_checked fusedMap2681_checked
    DegreeTwoThreeFiniteComparisons.comparison2681
#print axioms sourceMap2681_checked
#print axioms fusedMap2681_checked
#print axioms certified2681
def sourceMap2681swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2681swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2681swap_checked : acceptsGraphIso
    (source (graph core2681) (root 10) 4 0) DegreeTwoThreeSpectrum6696.graph sourceMap2681swap=true := by decide +kernel
theorem fusedMap2681swap_checked : acceptsGraphIso
    (fused (graph core2681) (root 10) 4 0) DegreeTwoThreeSpectrum5548.graph fusedMap2681swap=true := by decide +kernel
theorem certified2681swap : Certified (graph core2681) (root 10) 4 0 :=
  of_native_maps core2681 DegreeTwoThreeSpectrum6696.graph DegreeTwoThreeSpectrum5548.graph
    sourceMap2681swap fusedMap2681swap sourceMap2681swap_checked fusedMap2681swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2681
#print axioms sourceMap2681swap_checked
#print axioms fusedMap2681swap_checked
#print axioms certified2681swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
