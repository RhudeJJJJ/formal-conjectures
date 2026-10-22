/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2024 : Family 10 := level10.get ⟨1700,by decide⟩
def sourceMap2024 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2024 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2024_checked : acceptsGraphIso
    (source (graph core2024) (root 10) 0 2) DegreeTwoThreeSpectrum3818.graph sourceMap2024=true := by decide +kernel
theorem fusedMap2024_checked : acceptsGraphIso
    (fused (graph core2024) (root 10) 0 2) DegreeTwoThreeSpectrum3376.graph fusedMap2024=true := by decide +kernel
theorem certified2024 : Certified (graph core2024) (root 10) 0 2 :=
  of_native_maps core2024 DegreeTwoThreeSpectrum3818.graph DegreeTwoThreeSpectrum3376.graph
    sourceMap2024 fusedMap2024 sourceMap2024_checked fusedMap2024_checked
    DegreeTwoThreeFiniteComparisons.comparison2024
#print axioms sourceMap2024_checked
#print axioms fusedMap2024_checked
#print axioms certified2024
def sourceMap2024swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2024swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2024swap_checked : acceptsGraphIso
    (source (graph core2024) (root 10) 2 0) DegreeTwoThreeSpectrum3818.graph sourceMap2024swap=true := by decide +kernel
theorem fusedMap2024swap_checked : acceptsGraphIso
    (fused (graph core2024) (root 10) 2 0) DegreeTwoThreeSpectrum3376.graph fusedMap2024swap=true := by decide +kernel
theorem certified2024swap : Certified (graph core2024) (root 10) 2 0 :=
  of_native_maps core2024 DegreeTwoThreeSpectrum3818.graph DegreeTwoThreeSpectrum3376.graph
    sourceMap2024swap fusedMap2024swap sourceMap2024swap_checked fusedMap2024swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2024
#print axioms sourceMap2024swap_checked
#print axioms fusedMap2024swap_checked
#print axioms certified2024swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
