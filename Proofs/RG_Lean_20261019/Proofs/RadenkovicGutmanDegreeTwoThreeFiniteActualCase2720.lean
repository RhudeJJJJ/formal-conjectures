/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2720 : Family 10 := level10.get ⟨872,by decide⟩
def sourceMap2720 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2720 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2720_checked : acceptsGraphIso
    (source (graph core2720) (root 10) 0 4) DegreeTwoThreeSpectrum6930.graph sourceMap2720=true := by decide +kernel
theorem fusedMap2720_checked : acceptsGraphIso
    (fused (graph core2720) (root 10) 0 4) DegreeTwoThreeSpectrum5716.graph fusedMap2720=true := by decide +kernel
theorem certified2720 : Certified (graph core2720) (root 10) 0 4 :=
  of_native_maps core2720 DegreeTwoThreeSpectrum6930.graph DegreeTwoThreeSpectrum5716.graph
    sourceMap2720 fusedMap2720 sourceMap2720_checked fusedMap2720_checked
    DegreeTwoThreeFiniteComparisons.comparison2720
#print axioms sourceMap2720_checked
#print axioms fusedMap2720_checked
#print axioms certified2720
def sourceMap2720swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2720swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2720swap_checked : acceptsGraphIso
    (source (graph core2720) (root 10) 4 0) DegreeTwoThreeSpectrum6930.graph sourceMap2720swap=true := by decide +kernel
theorem fusedMap2720swap_checked : acceptsGraphIso
    (fused (graph core2720) (root 10) 4 0) DegreeTwoThreeSpectrum5716.graph fusedMap2720swap=true := by decide +kernel
theorem certified2720swap : Certified (graph core2720) (root 10) 4 0 :=
  of_native_maps core2720 DegreeTwoThreeSpectrum6930.graph DegreeTwoThreeSpectrum5716.graph
    sourceMap2720swap fusedMap2720swap sourceMap2720swap_checked fusedMap2720swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2720
#print axioms sourceMap2720swap_checked
#print axioms fusedMap2720swap_checked
#print axioms certified2720swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
