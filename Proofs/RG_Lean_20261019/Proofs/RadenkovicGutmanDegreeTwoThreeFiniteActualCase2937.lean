/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2937 : Family 10 := level10.get ⟨1408,by decide⟩
def sourceMap2937 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2937 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2937_checked : acceptsGraphIso
    (source (graph core2937) (root 10) 0 4) DegreeTwoThreeSpectrum6805.graph sourceMap2937=true := by decide +kernel
theorem fusedMap2937_checked : acceptsGraphIso
    (fused (graph core2937) (root 10) 0 4) DegreeTwoThreeSpectrum6808.graph fusedMap2937=true := by decide +kernel
theorem certified2937 : Certified (graph core2937) (root 10) 0 4 :=
  of_native_maps core2937 DegreeTwoThreeSpectrum6805.graph DegreeTwoThreeSpectrum6808.graph
    sourceMap2937 fusedMap2937 sourceMap2937_checked fusedMap2937_checked
    DegreeTwoThreeFiniteComparisons.comparison2937
#print axioms sourceMap2937_checked
#print axioms fusedMap2937_checked
#print axioms certified2937
def sourceMap2937swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2937swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2937swap_checked : acceptsGraphIso
    (source (graph core2937) (root 10) 4 0) DegreeTwoThreeSpectrum6805.graph sourceMap2937swap=true := by decide +kernel
theorem fusedMap2937swap_checked : acceptsGraphIso
    (fused (graph core2937) (root 10) 4 0) DegreeTwoThreeSpectrum6808.graph fusedMap2937swap=true := by decide +kernel
theorem certified2937swap : Certified (graph core2937) (root 10) 4 0 :=
  of_native_maps core2937 DegreeTwoThreeSpectrum6805.graph DegreeTwoThreeSpectrum6808.graph
    sourceMap2937swap fusedMap2937swap sourceMap2937swap_checked fusedMap2937swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2937
#print axioms sourceMap2937swap_checked
#print axioms fusedMap2937swap_checked
#print axioms certified2937swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
