/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2655 : Family 10 := level10.get ⟨694,by decide⟩
def sourceMap2655 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2655 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2655_checked : acceptsGraphIso
    (source (graph core2655) (root 10) 0 4) DegreeTwoThreeSpectrum6517.graph sourceMap2655=true := by decide +kernel
theorem fusedMap2655_checked : acceptsGraphIso
    (fused (graph core2655) (root 10) 0 4) DegreeTwoThreeSpectrum5430.graph fusedMap2655=true := by decide +kernel
theorem certified2655 : Certified (graph core2655) (root 10) 0 4 :=
  of_native_maps core2655 DegreeTwoThreeSpectrum6517.graph DegreeTwoThreeSpectrum5430.graph
    sourceMap2655 fusedMap2655 sourceMap2655_checked fusedMap2655_checked
    DegreeTwoThreeFiniteComparisons.comparison2655
#print axioms sourceMap2655_checked
#print axioms fusedMap2655_checked
#print axioms certified2655
def sourceMap2655swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2655swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2655swap_checked : acceptsGraphIso
    (source (graph core2655) (root 10) 4 0) DegreeTwoThreeSpectrum6517.graph sourceMap2655swap=true := by decide +kernel
theorem fusedMap2655swap_checked : acceptsGraphIso
    (fused (graph core2655) (root 10) 4 0) DegreeTwoThreeSpectrum5430.graph fusedMap2655swap=true := by decide +kernel
theorem certified2655swap : Certified (graph core2655) (root 10) 4 0 :=
  of_native_maps core2655 DegreeTwoThreeSpectrum6517.graph DegreeTwoThreeSpectrum5430.graph
    sourceMap2655swap fusedMap2655swap sourceMap2655swap_checked fusedMap2655swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2655
#print axioms sourceMap2655swap_checked
#print axioms fusedMap2655swap_checked
#print axioms certified2655swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
