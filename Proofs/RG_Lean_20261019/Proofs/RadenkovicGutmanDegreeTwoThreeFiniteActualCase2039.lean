/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2039 : Family 10 := level10.get ⟨1738,by decide⟩
def sourceMap2039 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap2039 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2039_checked : acceptsGraphIso
    (source (graph core2039) (root 10) 0 2) DegreeTwoThreeSpectrum3836.graph sourceMap2039=true := by decide +kernel
theorem fusedMap2039_checked : acceptsGraphIso
    (fused (graph core2039) (root 10) 0 2) DegreeTwoThreeSpectrum3460.graph fusedMap2039=true := by decide +kernel
theorem certified2039 : Certified (graph core2039) (root 10) 0 2 :=
  of_native_maps core2039 DegreeTwoThreeSpectrum3836.graph DegreeTwoThreeSpectrum3460.graph
    sourceMap2039 fusedMap2039 sourceMap2039_checked fusedMap2039_checked
    DegreeTwoThreeFiniteComparisons.comparison2039
#print axioms sourceMap2039_checked
#print axioms fusedMap2039_checked
#print axioms certified2039
def sourceMap2039swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap2039swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2039swap_checked : acceptsGraphIso
    (source (graph core2039) (root 10) 2 0) DegreeTwoThreeSpectrum3836.graph sourceMap2039swap=true := by decide +kernel
theorem fusedMap2039swap_checked : acceptsGraphIso
    (fused (graph core2039) (root 10) 2 0) DegreeTwoThreeSpectrum3460.graph fusedMap2039swap=true := by decide +kernel
theorem certified2039swap : Certified (graph core2039) (root 10) 2 0 :=
  of_native_maps core2039 DegreeTwoThreeSpectrum3836.graph DegreeTwoThreeSpectrum3460.graph
    sourceMap2039swap fusedMap2039swap sourceMap2039swap_checked fusedMap2039swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2039
#print axioms sourceMap2039swap_checked
#print axioms fusedMap2039swap_checked
#print axioms certified2039swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
