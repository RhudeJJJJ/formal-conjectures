/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2746 : Family 10 := level10.get ⟨942,by decide⟩
def sourceMap2746 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2746 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2746_checked : acceptsGraphIso
    (source (graph core2746) (root 10) 0 4) DegreeTwoThreeSpectrum7024.graph sourceMap2746=true := by decide +kernel
theorem fusedMap2746_checked : acceptsGraphIso
    (fused (graph core2746) (root 10) 0 4) DegreeTwoThreeSpectrum5841.graph fusedMap2746=true := by decide +kernel
theorem certified2746 : Certified (graph core2746) (root 10) 0 4 :=
  of_native_maps core2746 DegreeTwoThreeSpectrum7024.graph DegreeTwoThreeSpectrum5841.graph
    sourceMap2746 fusedMap2746 sourceMap2746_checked fusedMap2746_checked
    DegreeTwoThreeFiniteComparisons.comparison2746
#print axioms sourceMap2746_checked
#print axioms fusedMap2746_checked
#print axioms certified2746
def sourceMap2746swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2746swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2746swap_checked : acceptsGraphIso
    (source (graph core2746) (root 10) 4 0) DegreeTwoThreeSpectrum7024.graph sourceMap2746swap=true := by decide +kernel
theorem fusedMap2746swap_checked : acceptsGraphIso
    (fused (graph core2746) (root 10) 4 0) DegreeTwoThreeSpectrum5841.graph fusedMap2746swap=true := by decide +kernel
theorem certified2746swap : Certified (graph core2746) (root 10) 4 0 :=
  of_native_maps core2746 DegreeTwoThreeSpectrum7024.graph DegreeTwoThreeSpectrum5841.graph
    sourceMap2746swap fusedMap2746swap sourceMap2746swap_checked fusedMap2746swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2746
#print axioms sourceMap2746swap_checked
#print axioms fusedMap2746swap_checked
#print axioms certified2746swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
