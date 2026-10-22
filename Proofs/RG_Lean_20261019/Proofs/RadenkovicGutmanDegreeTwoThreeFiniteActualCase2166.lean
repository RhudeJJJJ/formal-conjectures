/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2166 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap2166 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2166 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2166_checked : acceptsGraphIso
    (source (graph core2166) (root 8) 0 4) DegreeTwoThreeSpectrum2755.graph sourceMap2166=true := by decide +kernel
theorem fusedMap2166_checked : acceptsGraphIso
    (fused (graph core2166) (root 8) 0 4) DegreeTwoThreeSpectrum2757.graph fusedMap2166=true := by decide +kernel
theorem certified2166 : Certified (graph core2166) (root 8) 0 4 :=
  of_native_maps core2166 DegreeTwoThreeSpectrum2755.graph DegreeTwoThreeSpectrum2757.graph
    sourceMap2166 fusedMap2166 sourceMap2166_checked fusedMap2166_checked
    DegreeTwoThreeFiniteComparisons.comparison2166
#print axioms sourceMap2166_checked
#print axioms fusedMap2166_checked
#print axioms certified2166
def sourceMap2166swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2166swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2166swap_checked : acceptsGraphIso
    (source (graph core2166) (root 8) 4 0) DegreeTwoThreeSpectrum2755.graph sourceMap2166swap=true := by decide +kernel
theorem fusedMap2166swap_checked : acceptsGraphIso
    (fused (graph core2166) (root 8) 4 0) DegreeTwoThreeSpectrum2757.graph fusedMap2166swap=true := by decide +kernel
theorem certified2166swap : Certified (graph core2166) (root 8) 4 0 :=
  of_native_maps core2166 DegreeTwoThreeSpectrum2755.graph DegreeTwoThreeSpectrum2757.graph
    sourceMap2166swap fusedMap2166swap sourceMap2166swap_checked fusedMap2166swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2166
#print axioms sourceMap2166swap_checked
#print axioms fusedMap2166swap_checked
#print axioms certified2166swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
