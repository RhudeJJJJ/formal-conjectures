/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2153 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap2153 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2153 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2153_checked : acceptsGraphIso
    (source (graph core2153) (root 8) 0 4) DegreeTwoThreeSpectrum2573.graph sourceMap2153=true := by decide +kernel
theorem fusedMap2153_checked : acceptsGraphIso
    (fused (graph core2153) (root 8) 0 4) DegreeTwoThreeSpectrum2575.graph fusedMap2153=true := by decide +kernel
theorem certified2153 : Certified (graph core2153) (root 8) 0 4 :=
  of_native_maps core2153 DegreeTwoThreeSpectrum2573.graph DegreeTwoThreeSpectrum2575.graph
    sourceMap2153 fusedMap2153 sourceMap2153_checked fusedMap2153_checked
    DegreeTwoThreeFiniteComparisons.comparison2153
#print axioms sourceMap2153_checked
#print axioms fusedMap2153_checked
#print axioms certified2153
def sourceMap2153swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2153swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2153swap_checked : acceptsGraphIso
    (source (graph core2153) (root 8) 4 0) DegreeTwoThreeSpectrum2573.graph sourceMap2153swap=true := by decide +kernel
theorem fusedMap2153swap_checked : acceptsGraphIso
    (fused (graph core2153) (root 8) 4 0) DegreeTwoThreeSpectrum2575.graph fusedMap2153swap=true := by decide +kernel
theorem certified2153swap : Certified (graph core2153) (root 8) 4 0 :=
  of_native_maps core2153 DegreeTwoThreeSpectrum2573.graph DegreeTwoThreeSpectrum2575.graph
    sourceMap2153swap fusedMap2153swap sourceMap2153swap_checked fusedMap2153swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2153
#print axioms sourceMap2153swap_checked
#print axioms fusedMap2153swap_checked
#print axioms certified2153swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
