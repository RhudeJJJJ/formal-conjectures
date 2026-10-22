/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2203 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap2203 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2203 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2203_checked : acceptsGraphIso
    (source (graph core2203) (root 8) 0 4) DegreeTwoThreeSpectrum3426.graph sourceMap2203=true := by decide +kernel
theorem fusedMap2203_checked : acceptsGraphIso
    (fused (graph core2203) (root 8) 0 4) DegreeTwoThreeSpectrum2662.graph fusedMap2203=true := by decide +kernel
theorem certified2203 : Certified (graph core2203) (root 8) 0 4 :=
  of_native_maps core2203 DegreeTwoThreeSpectrum3426.graph DegreeTwoThreeSpectrum2662.graph
    sourceMap2203 fusedMap2203 sourceMap2203_checked fusedMap2203_checked
    DegreeTwoThreeFiniteComparisons.comparison2203
#print axioms sourceMap2203_checked
#print axioms fusedMap2203_checked
#print axioms certified2203
def sourceMap2203swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2203swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2203swap_checked : acceptsGraphIso
    (source (graph core2203) (root 8) 4 0) DegreeTwoThreeSpectrum3426.graph sourceMap2203swap=true := by decide +kernel
theorem fusedMap2203swap_checked : acceptsGraphIso
    (fused (graph core2203) (root 8) 4 0) DegreeTwoThreeSpectrum2662.graph fusedMap2203swap=true := by decide +kernel
theorem certified2203swap : Certified (graph core2203) (root 8) 4 0 :=
  of_native_maps core2203 DegreeTwoThreeSpectrum3426.graph DegreeTwoThreeSpectrum2662.graph
    sourceMap2203swap fusedMap2203swap sourceMap2203swap_checked fusedMap2203swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2203
#print axioms sourceMap2203swap_checked
#print axioms fusedMap2203swap_checked
#print axioms certified2203swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
