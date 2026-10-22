/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2135 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap2135 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 8 0 4 v)
def fusedMap2135 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2135_checked : acceptsGraphIso
    (source (graph core2135) (root 8) 0 4) DegreeTwoThreeSpectrum2814.graph sourceMap2135=true := by decide +kernel
theorem fusedMap2135_checked : acceptsGraphIso
    (fused (graph core2135) (root 8) 0 4) DegreeTwoThreeSpectrum2371.graph fusedMap2135=true := by decide +kernel
theorem certified2135 : Certified (graph core2135) (root 8) 0 4 :=
  of_native_maps core2135 DegreeTwoThreeSpectrum2814.graph DegreeTwoThreeSpectrum2371.graph
    sourceMap2135 fusedMap2135 sourceMap2135_checked fusedMap2135_checked
    DegreeTwoThreeFiniteComparisons.comparison2135
#print axioms sourceMap2135_checked
#print axioms fusedMap2135_checked
#print axioms certified2135
def sourceMap2135swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14] (sourceLabel 8 4 0 v)
def fusedMap2135swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2135swap_checked : acceptsGraphIso
    (source (graph core2135) (root 8) 4 0) DegreeTwoThreeSpectrum2814.graph sourceMap2135swap=true := by decide +kernel
theorem fusedMap2135swap_checked : acceptsGraphIso
    (fused (graph core2135) (root 8) 4 0) DegreeTwoThreeSpectrum2371.graph fusedMap2135swap=true := by decide +kernel
theorem certified2135swap : Certified (graph core2135) (root 8) 4 0 :=
  of_native_maps core2135 DegreeTwoThreeSpectrum2814.graph DegreeTwoThreeSpectrum2371.graph
    sourceMap2135swap fusedMap2135swap sourceMap2135swap_checked fusedMap2135swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2135
#print axioms sourceMap2135swap_checked
#print axioms fusedMap2135swap_checked
#print axioms certified2135swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
