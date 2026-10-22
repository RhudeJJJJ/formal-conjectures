/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2021 : Family 10 := level10.get ⟨1678,by decide⟩
def sourceMap2021 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2021 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2021_checked : acceptsGraphIso
    (source (graph core2021) (root 10) 0 2) DegreeTwoThreeSpectrum3813.graph sourceMap2021=true := by decide +kernel
theorem fusedMap2021_checked : acceptsGraphIso
    (fused (graph core2021) (root 10) 0 2) DegreeTwoThreeSpectrum3282.graph fusedMap2021=true := by decide +kernel
theorem certified2021 : Certified (graph core2021) (root 10) 0 2 :=
  of_native_maps core2021 DegreeTwoThreeSpectrum3813.graph DegreeTwoThreeSpectrum3282.graph
    sourceMap2021 fusedMap2021 sourceMap2021_checked fusedMap2021_checked
    DegreeTwoThreeFiniteComparisons.comparison2021
#print axioms sourceMap2021_checked
#print axioms fusedMap2021_checked
#print axioms certified2021
def sourceMap2021swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2021swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2021swap_checked : acceptsGraphIso
    (source (graph core2021) (root 10) 2 0) DegreeTwoThreeSpectrum3813.graph sourceMap2021swap=true := by decide +kernel
theorem fusedMap2021swap_checked : acceptsGraphIso
    (fused (graph core2021) (root 10) 2 0) DegreeTwoThreeSpectrum3282.graph fusedMap2021swap=true := by decide +kernel
theorem certified2021swap : Certified (graph core2021) (root 10) 2 0 :=
  of_native_maps core2021 DegreeTwoThreeSpectrum3813.graph DegreeTwoThreeSpectrum3282.graph
    sourceMap2021swap fusedMap2021swap sourceMap2021swap_checked fusedMap2021swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2021
#print axioms sourceMap2021swap_checked
#print axioms fusedMap2021swap_checked
#print axioms certified2021swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
