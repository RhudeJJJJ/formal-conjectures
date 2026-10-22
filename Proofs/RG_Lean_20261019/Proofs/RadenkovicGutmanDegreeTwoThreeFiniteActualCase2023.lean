/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2023 : Family 10 := level10.get ⟨1688,by decide⟩
def sourceMap2023 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,14,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap2023 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2023_checked : acceptsGraphIso
    (source (graph core2023) (root 10) 0 2) DegreeTwoThreeSpectrum3817.graph sourceMap2023=true := by decide +kernel
theorem fusedMap2023_checked : acceptsGraphIso
    (fused (graph core2023) (root 10) 0 2) DegreeTwoThreeSpectrum3302.graph fusedMap2023=true := by decide +kernel
theorem certified2023 : Certified (graph core2023) (root 10) 0 2 :=
  of_native_maps core2023 DegreeTwoThreeSpectrum3817.graph DegreeTwoThreeSpectrum3302.graph
    sourceMap2023 fusedMap2023 sourceMap2023_checked fusedMap2023_checked
    DegreeTwoThreeFiniteComparisons.comparison2023
#print axioms sourceMap2023_checked
#print axioms fusedMap2023_checked
#print axioms certified2023
def sourceMap2023swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,5,6,7,14] (sourceLabel 10 2 0 v)
def fusedMap2023swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2023swap_checked : acceptsGraphIso
    (source (graph core2023) (root 10) 2 0) DegreeTwoThreeSpectrum3817.graph sourceMap2023swap=true := by decide +kernel
theorem fusedMap2023swap_checked : acceptsGraphIso
    (fused (graph core2023) (root 10) 2 0) DegreeTwoThreeSpectrum3302.graph fusedMap2023swap=true := by decide +kernel
theorem certified2023swap : Certified (graph core2023) (root 10) 2 0 :=
  of_native_maps core2023 DegreeTwoThreeSpectrum3817.graph DegreeTwoThreeSpectrum3302.graph
    sourceMap2023swap fusedMap2023swap sourceMap2023swap_checked fusedMap2023swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2023
#print axioms sourceMap2023swap_checked
#print axioms fusedMap2023swap_checked
#print axioms certified2023swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
