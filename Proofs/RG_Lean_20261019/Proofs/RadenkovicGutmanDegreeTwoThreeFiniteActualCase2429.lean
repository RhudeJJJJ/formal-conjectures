/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2429 : Family 9 := level9.get ⟨609,by decide⟩
def sourceMap2429 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2429 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2429_checked : acceptsGraphIso
    (source (graph core2429) (root 9) 0 4) DegreeTwoThreeSpectrum4745.graph sourceMap2429=true := by decide +kernel
theorem fusedMap2429_checked : acceptsGraphIso
    (fused (graph core2429) (root 9) 0 4) DegreeTwoThreeSpectrum4304.graph fusedMap2429=true := by decide +kernel
theorem certified2429 : Certified (graph core2429) (root 9) 0 4 :=
  of_native_maps core2429 DegreeTwoThreeSpectrum4745.graph DegreeTwoThreeSpectrum4304.graph
    sourceMap2429 fusedMap2429 sourceMap2429_checked fusedMap2429_checked
    DegreeTwoThreeFiniteComparisons.comparison2429
#print axioms sourceMap2429_checked
#print axioms fusedMap2429_checked
#print axioms certified2429
def sourceMap2429swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2429swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2429swap_checked : acceptsGraphIso
    (source (graph core2429) (root 9) 4 0) DegreeTwoThreeSpectrum4745.graph sourceMap2429swap=true := by decide +kernel
theorem fusedMap2429swap_checked : acceptsGraphIso
    (fused (graph core2429) (root 9) 4 0) DegreeTwoThreeSpectrum4304.graph fusedMap2429swap=true := by decide +kernel
theorem certified2429swap : Certified (graph core2429) (root 9) 4 0 :=
  of_native_maps core2429 DegreeTwoThreeSpectrum4745.graph DegreeTwoThreeSpectrum4304.graph
    sourceMap2429swap fusedMap2429swap sourceMap2429swap_checked fusedMap2429swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2429
#print axioms sourceMap2429swap_checked
#print axioms fusedMap2429swap_checked
#print axioms certified2429swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
