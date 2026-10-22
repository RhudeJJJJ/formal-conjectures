/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2571 : Family 10 := level10.get ⟨449,by decide⟩
def sourceMap2571 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2571 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2571_checked : acceptsGraphIso
    (source (graph core2571) (root 10) 0 4) DegreeTwoThreeSpectrum5872.graph sourceMap2571=true := by decide +kernel
theorem fusedMap2571_checked : acceptsGraphIso
    (fused (graph core2571) (root 10) 0 4) DegreeTwoThreeSpectrum5873.graph fusedMap2571=true := by decide +kernel
theorem certified2571 : Certified (graph core2571) (root 10) 0 4 :=
  of_native_maps core2571 DegreeTwoThreeSpectrum5872.graph DegreeTwoThreeSpectrum5873.graph
    sourceMap2571 fusedMap2571 sourceMap2571_checked fusedMap2571_checked
    DegreeTwoThreeFiniteComparisons.comparison2571
#print axioms sourceMap2571_checked
#print axioms fusedMap2571_checked
#print axioms certified2571
def sourceMap2571swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2571swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2571swap_checked : acceptsGraphIso
    (source (graph core2571) (root 10) 4 0) DegreeTwoThreeSpectrum5872.graph sourceMap2571swap=true := by decide +kernel
theorem fusedMap2571swap_checked : acceptsGraphIso
    (fused (graph core2571) (root 10) 4 0) DegreeTwoThreeSpectrum5873.graph fusedMap2571swap=true := by decide +kernel
theorem certified2571swap : Certified (graph core2571) (root 10) 4 0 :=
  of_native_maps core2571 DegreeTwoThreeSpectrum5872.graph DegreeTwoThreeSpectrum5873.graph
    sourceMap2571swap fusedMap2571swap sourceMap2571swap_checked fusedMap2571swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2571
#print axioms sourceMap2571swap_checked
#print axioms fusedMap2571swap_checked
#print axioms certified2571swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
