/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2650 : Family 10 := level10.get ⟨675,by decide⟩
def sourceMap2650 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2650 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2650_checked : acceptsGraphIso
    (source (graph core2650) (root 10) 0 4) DegreeTwoThreeSpectrum6464.graph sourceMap2650=true := by decide +kernel
theorem fusedMap2650_checked : acceptsGraphIso
    (fused (graph core2650) (root 10) 0 4) DegreeTwoThreeSpectrum5397.graph fusedMap2650=true := by decide +kernel
theorem certified2650 : Certified (graph core2650) (root 10) 0 4 :=
  of_native_maps core2650 DegreeTwoThreeSpectrum6464.graph DegreeTwoThreeSpectrum5397.graph
    sourceMap2650 fusedMap2650 sourceMap2650_checked fusedMap2650_checked
    DegreeTwoThreeFiniteComparisons.comparison2650
#print axioms sourceMap2650_checked
#print axioms fusedMap2650_checked
#print axioms certified2650
def sourceMap2650swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2650swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2650swap_checked : acceptsGraphIso
    (source (graph core2650) (root 10) 4 0) DegreeTwoThreeSpectrum6464.graph sourceMap2650swap=true := by decide +kernel
theorem fusedMap2650swap_checked : acceptsGraphIso
    (fused (graph core2650) (root 10) 4 0) DegreeTwoThreeSpectrum5397.graph fusedMap2650swap=true := by decide +kernel
theorem certified2650swap : Certified (graph core2650) (root 10) 4 0 :=
  of_native_maps core2650 DegreeTwoThreeSpectrum6464.graph DegreeTwoThreeSpectrum5397.graph
    sourceMap2650swap fusedMap2650swap sourceMap2650swap_checked fusedMap2650swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2650
#print axioms sourceMap2650swap_checked
#print axioms fusedMap2650swap_checked
#print axioms certified2650swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
