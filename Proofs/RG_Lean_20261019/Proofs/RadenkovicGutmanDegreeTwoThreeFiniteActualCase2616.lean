/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2616 : Family 10 := level10.get ⟨584,by decide⟩
def sourceMap2616 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2616 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2616_checked : acceptsGraphIso
    (source (graph core2616) (root 10) 0 4) DegreeTwoThreeSpectrum6269.graph sourceMap2616=true := by decide +kernel
theorem fusedMap2616_checked : acceptsGraphIso
    (fused (graph core2616) (root 10) 0 4) DegreeTwoThreeSpectrum5253.graph fusedMap2616=true := by decide +kernel
theorem certified2616 : Certified (graph core2616) (root 10) 0 4 :=
  of_native_maps core2616 DegreeTwoThreeSpectrum6269.graph DegreeTwoThreeSpectrum5253.graph
    sourceMap2616 fusedMap2616 sourceMap2616_checked fusedMap2616_checked
    DegreeTwoThreeFiniteComparisons.comparison2616
#print axioms sourceMap2616_checked
#print axioms fusedMap2616_checked
#print axioms certified2616
def sourceMap2616swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2616swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2616swap_checked : acceptsGraphIso
    (source (graph core2616) (root 10) 4 0) DegreeTwoThreeSpectrum6269.graph sourceMap2616swap=true := by decide +kernel
theorem fusedMap2616swap_checked : acceptsGraphIso
    (fused (graph core2616) (root 10) 4 0) DegreeTwoThreeSpectrum5253.graph fusedMap2616swap=true := by decide +kernel
theorem certified2616swap : Certified (graph core2616) (root 10) 4 0 :=
  of_native_maps core2616 DegreeTwoThreeSpectrum6269.graph DegreeTwoThreeSpectrum5253.graph
    sourceMap2616swap fusedMap2616swap sourceMap2616swap_checked fusedMap2616swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2616
#print axioms sourceMap2616swap_checked
#print axioms fusedMap2616swap_checked
#print axioms certified2616swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
