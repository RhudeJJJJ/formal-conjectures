/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2137 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap2137 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2137 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2137_checked : acceptsGraphIso
    (source (graph core2137) (root 8) 0 4) DegreeTwoThreeSpectrum2909.graph sourceMap2137=true := by decide +kernel
theorem fusedMap2137_checked : acceptsGraphIso
    (fused (graph core2137) (root 8) 0 4) DegreeTwoThreeSpectrum2389.graph fusedMap2137=true := by decide +kernel
theorem certified2137 : Certified (graph core2137) (root 8) 0 4 :=
  of_native_maps core2137 DegreeTwoThreeSpectrum2909.graph DegreeTwoThreeSpectrum2389.graph
    sourceMap2137 fusedMap2137 sourceMap2137_checked fusedMap2137_checked
    DegreeTwoThreeFiniteComparisons.comparison2137
#print axioms sourceMap2137_checked
#print axioms fusedMap2137_checked
#print axioms certified2137
def sourceMap2137swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2137swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2137swap_checked : acceptsGraphIso
    (source (graph core2137) (root 8) 4 0) DegreeTwoThreeSpectrum2909.graph sourceMap2137swap=true := by decide +kernel
theorem fusedMap2137swap_checked : acceptsGraphIso
    (fused (graph core2137) (root 8) 4 0) DegreeTwoThreeSpectrum2389.graph fusedMap2137swap=true := by decide +kernel
theorem certified2137swap : Certified (graph core2137) (root 8) 4 0 :=
  of_native_maps core2137 DegreeTwoThreeSpectrum2909.graph DegreeTwoThreeSpectrum2389.graph
    sourceMap2137swap fusedMap2137swap sourceMap2137swap_checked fusedMap2137swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2137
#print axioms sourceMap2137swap_checked
#print axioms fusedMap2137swap_checked
#print axioms certified2137swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
