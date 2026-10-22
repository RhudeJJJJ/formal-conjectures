/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2646 : Family 10 := level10.get ⟨668,by decide⟩
def sourceMap2646 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2646 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2646_checked : acceptsGraphIso
    (source (graph core2646) (root 10) 0 4) DegreeTwoThreeSpectrum6448.graph sourceMap2646=true := by decide +kernel
theorem fusedMap2646_checked : acceptsGraphIso
    (fused (graph core2646) (root 10) 0 4) DegreeTwoThreeSpectrum5380.graph fusedMap2646=true := by decide +kernel
theorem certified2646 : Certified (graph core2646) (root 10) 0 4 :=
  of_native_maps core2646 DegreeTwoThreeSpectrum6448.graph DegreeTwoThreeSpectrum5380.graph
    sourceMap2646 fusedMap2646 sourceMap2646_checked fusedMap2646_checked
    DegreeTwoThreeFiniteComparisons.comparison2646
#print axioms sourceMap2646_checked
#print axioms fusedMap2646_checked
#print axioms certified2646
def sourceMap2646swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2646swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2646swap_checked : acceptsGraphIso
    (source (graph core2646) (root 10) 4 0) DegreeTwoThreeSpectrum6448.graph sourceMap2646swap=true := by decide +kernel
theorem fusedMap2646swap_checked : acceptsGraphIso
    (fused (graph core2646) (root 10) 4 0) DegreeTwoThreeSpectrum5380.graph fusedMap2646swap=true := by decide +kernel
theorem certified2646swap : Certified (graph core2646) (root 10) 4 0 :=
  of_native_maps core2646 DegreeTwoThreeSpectrum6448.graph DegreeTwoThreeSpectrum5380.graph
    sourceMap2646swap fusedMap2646swap sourceMap2646swap_checked fusedMap2646swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2646
#print axioms sourceMap2646swap_checked
#print axioms fusedMap2646swap_checked
#print axioms certified2646swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
