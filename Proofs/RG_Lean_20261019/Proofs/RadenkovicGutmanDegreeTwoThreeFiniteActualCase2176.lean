/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2176 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap2176 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2176 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2176_checked : acceptsGraphIso
    (source (graph core2176) (root 8) 0 4) DegreeTwoThreeSpectrum2914.graph sourceMap2176=true := by decide +kernel
theorem fusedMap2176_checked : acceptsGraphIso
    (fused (graph core2176) (root 8) 0 4) DegreeTwoThreeSpectrum2916.graph fusedMap2176=true := by decide +kernel
theorem certified2176 : Certified (graph core2176) (root 8) 0 4 :=
  of_native_maps core2176 DegreeTwoThreeSpectrum2914.graph DegreeTwoThreeSpectrum2916.graph
    sourceMap2176 fusedMap2176 sourceMap2176_checked fusedMap2176_checked
    DegreeTwoThreeFiniteComparisons.comparison2176
#print axioms sourceMap2176_checked
#print axioms fusedMap2176_checked
#print axioms certified2176
def sourceMap2176swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2176swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2176swap_checked : acceptsGraphIso
    (source (graph core2176) (root 8) 4 0) DegreeTwoThreeSpectrum2914.graph sourceMap2176swap=true := by decide +kernel
theorem fusedMap2176swap_checked : acceptsGraphIso
    (fused (graph core2176) (root 8) 4 0) DegreeTwoThreeSpectrum2916.graph fusedMap2176swap=true := by decide +kernel
theorem certified2176swap : Certified (graph core2176) (root 8) 4 0 :=
  of_native_maps core2176 DegreeTwoThreeSpectrum2914.graph DegreeTwoThreeSpectrum2916.graph
    sourceMap2176swap fusedMap2176swap sourceMap2176swap_checked fusedMap2176swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2176
#print axioms sourceMap2176swap_checked
#print axioms fusedMap2176swap_checked
#print axioms certified2176swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
