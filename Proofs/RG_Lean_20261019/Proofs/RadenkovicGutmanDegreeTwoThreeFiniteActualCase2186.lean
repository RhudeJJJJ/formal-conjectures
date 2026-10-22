/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2186 : Family 8 := level8.get ⟨201,by decide⟩
def sourceMap2186 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2186 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2186_checked : acceptsGraphIso
    (source (graph core2186) (root 8) 0 4) DegreeTwoThreeSpectrum3098.graph sourceMap2186=true := by decide +kernel
theorem fusedMap2186_checked : acceptsGraphIso
    (fused (graph core2186) (root 8) 0 4) DegreeTwoThreeSpectrum2463.graph fusedMap2186=true := by decide +kernel
theorem certified2186 : Certified (graph core2186) (root 8) 0 4 :=
  of_native_maps core2186 DegreeTwoThreeSpectrum3098.graph DegreeTwoThreeSpectrum2463.graph
    sourceMap2186 fusedMap2186 sourceMap2186_checked fusedMap2186_checked
    DegreeTwoThreeFiniteComparisons.comparison2186
#print axioms sourceMap2186_checked
#print axioms fusedMap2186_checked
#print axioms certified2186
def sourceMap2186swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2186swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2186swap_checked : acceptsGraphIso
    (source (graph core2186) (root 8) 4 0) DegreeTwoThreeSpectrum3098.graph sourceMap2186swap=true := by decide +kernel
theorem fusedMap2186swap_checked : acceptsGraphIso
    (fused (graph core2186) (root 8) 4 0) DegreeTwoThreeSpectrum2463.graph fusedMap2186swap=true := by decide +kernel
theorem certified2186swap : Certified (graph core2186) (root 8) 4 0 :=
  of_native_maps core2186 DegreeTwoThreeSpectrum3098.graph DegreeTwoThreeSpectrum2463.graph
    sourceMap2186swap fusedMap2186swap sourceMap2186swap_checked fusedMap2186swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2186
#print axioms sourceMap2186swap_checked
#print axioms fusedMap2186swap_checked
#print axioms certified2186swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
