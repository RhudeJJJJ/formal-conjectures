/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2167 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap2167 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2167 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2167_checked : acceptsGraphIso
    (source (graph core2167) (root 8) 0 4) DegreeTwoThreeSpectrum2772.graph sourceMap2167=true := by decide +kernel
theorem fusedMap2167_checked : acceptsGraphIso
    (fused (graph core2167) (root 8) 0 4) DegreeTwoThreeSpectrum2774.graph fusedMap2167=true := by decide +kernel
theorem certified2167 : Certified (graph core2167) (root 8) 0 4 :=
  of_native_maps core2167 DegreeTwoThreeSpectrum2772.graph DegreeTwoThreeSpectrum2774.graph
    sourceMap2167 fusedMap2167 sourceMap2167_checked fusedMap2167_checked
    DegreeTwoThreeFiniteComparisons.comparison2167
#print axioms sourceMap2167_checked
#print axioms fusedMap2167_checked
#print axioms certified2167
def sourceMap2167swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2167swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2167swap_checked : acceptsGraphIso
    (source (graph core2167) (root 8) 4 0) DegreeTwoThreeSpectrum2772.graph sourceMap2167swap=true := by decide +kernel
theorem fusedMap2167swap_checked : acceptsGraphIso
    (fused (graph core2167) (root 8) 4 0) DegreeTwoThreeSpectrum2774.graph fusedMap2167swap=true := by decide +kernel
theorem certified2167swap : Certified (graph core2167) (root 8) 4 0 :=
  of_native_maps core2167 DegreeTwoThreeSpectrum2772.graph DegreeTwoThreeSpectrum2774.graph
    sourceMap2167swap fusedMap2167swap sourceMap2167swap_checked fusedMap2167swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2167
#print axioms sourceMap2167swap_checked
#print axioms fusedMap2167swap_checked
#print axioms certified2167swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
