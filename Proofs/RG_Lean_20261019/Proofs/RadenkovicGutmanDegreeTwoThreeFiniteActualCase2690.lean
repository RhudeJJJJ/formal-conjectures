/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2690 : Family 10 := level10.get ⟨794,by decide⟩
def sourceMap2690 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2690 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2690_checked : acceptsGraphIso
    (source (graph core2690) (root 10) 0 4) DegreeTwoThreeSpectrum6741.graph sourceMap2690=true := by decide +kernel
theorem fusedMap2690_checked : acceptsGraphIso
    (fused (graph core2690) (root 10) 0 4) DegreeTwoThreeSpectrum5580.graph fusedMap2690=true := by decide +kernel
theorem certified2690 : Certified (graph core2690) (root 10) 0 4 :=
  of_native_maps core2690 DegreeTwoThreeSpectrum6741.graph DegreeTwoThreeSpectrum5580.graph
    sourceMap2690 fusedMap2690 sourceMap2690_checked fusedMap2690_checked
    DegreeTwoThreeFiniteComparisons.comparison2690
#print axioms sourceMap2690_checked
#print axioms fusedMap2690_checked
#print axioms certified2690
def sourceMap2690swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2690swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2690swap_checked : acceptsGraphIso
    (source (graph core2690) (root 10) 4 0) DegreeTwoThreeSpectrum6741.graph sourceMap2690swap=true := by decide +kernel
theorem fusedMap2690swap_checked : acceptsGraphIso
    (fused (graph core2690) (root 10) 4 0) DegreeTwoThreeSpectrum5580.graph fusedMap2690swap=true := by decide +kernel
theorem certified2690swap : Certified (graph core2690) (root 10) 4 0 :=
  of_native_maps core2690 DegreeTwoThreeSpectrum6741.graph DegreeTwoThreeSpectrum5580.graph
    sourceMap2690swap fusedMap2690swap sourceMap2690swap_checked fusedMap2690swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2690
#print axioms sourceMap2690swap_checked
#print axioms fusedMap2690swap_checked
#print axioms certified2690swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
