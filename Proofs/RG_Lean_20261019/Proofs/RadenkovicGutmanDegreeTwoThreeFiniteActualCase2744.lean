/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2744 : Family 10 := level10.get ⟨937,by decide⟩
def sourceMap2744 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2744 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2744_checked : acceptsGraphIso
    (source (graph core2744) (root 10) 0 4) DegreeTwoThreeSpectrum7019.graph sourceMap2744=true := by decide +kernel
theorem fusedMap2744_checked : acceptsGraphIso
    (fused (graph core2744) (root 10) 0 4) DegreeTwoThreeSpectrum5832.graph fusedMap2744=true := by decide +kernel
theorem certified2744 : Certified (graph core2744) (root 10) 0 4 :=
  of_native_maps core2744 DegreeTwoThreeSpectrum7019.graph DegreeTwoThreeSpectrum5832.graph
    sourceMap2744 fusedMap2744 sourceMap2744_checked fusedMap2744_checked
    DegreeTwoThreeFiniteComparisons.comparison2744
#print axioms sourceMap2744_checked
#print axioms fusedMap2744_checked
#print axioms certified2744
def sourceMap2744swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2744swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2744swap_checked : acceptsGraphIso
    (source (graph core2744) (root 10) 4 0) DegreeTwoThreeSpectrum7019.graph sourceMap2744swap=true := by decide +kernel
theorem fusedMap2744swap_checked : acceptsGraphIso
    (fused (graph core2744) (root 10) 4 0) DegreeTwoThreeSpectrum5832.graph fusedMap2744swap=true := by decide +kernel
theorem certified2744swap : Certified (graph core2744) (root 10) 4 0 :=
  of_native_maps core2744 DegreeTwoThreeSpectrum7019.graph DegreeTwoThreeSpectrum5832.graph
    sourceMap2744swap fusedMap2744swap sourceMap2744swap_checked fusedMap2744swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2744
#print axioms sourceMap2744swap_checked
#print axioms fusedMap2744swap_checked
#print axioms certified2744swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
