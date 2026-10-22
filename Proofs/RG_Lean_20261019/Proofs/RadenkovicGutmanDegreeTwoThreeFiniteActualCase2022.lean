/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2022 : Family 10 := level10.get ⟨1680,by decide⟩
def sourceMap2022 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2022 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2022_checked : acceptsGraphIso
    (source (graph core2022) (root 10) 0 2) DegreeTwoThreeSpectrum3814.graph sourceMap2022=true := by decide +kernel
theorem fusedMap2022_checked : acceptsGraphIso
    (fused (graph core2022) (root 10) 0 2) DegreeTwoThreeSpectrum3283.graph fusedMap2022=true := by decide +kernel
theorem certified2022 : Certified (graph core2022) (root 10) 0 2 :=
  of_native_maps core2022 DegreeTwoThreeSpectrum3814.graph DegreeTwoThreeSpectrum3283.graph
    sourceMap2022 fusedMap2022 sourceMap2022_checked fusedMap2022_checked
    DegreeTwoThreeFiniteComparisons.comparison2022
#print axioms sourceMap2022_checked
#print axioms fusedMap2022_checked
#print axioms certified2022
def sourceMap2022swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2022swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2022swap_checked : acceptsGraphIso
    (source (graph core2022) (root 10) 2 0) DegreeTwoThreeSpectrum3814.graph sourceMap2022swap=true := by decide +kernel
theorem fusedMap2022swap_checked : acceptsGraphIso
    (fused (graph core2022) (root 10) 2 0) DegreeTwoThreeSpectrum3283.graph fusedMap2022swap=true := by decide +kernel
theorem certified2022swap : Certified (graph core2022) (root 10) 2 0 :=
  of_native_maps core2022 DegreeTwoThreeSpectrum3814.graph DegreeTwoThreeSpectrum3283.graph
    sourceMap2022swap fusedMap2022swap sourceMap2022swap_checked fusedMap2022swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2022
#print axioms sourceMap2022swap_checked
#print axioms fusedMap2022swap_checked
#print axioms certified2022swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
