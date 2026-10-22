/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2210 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap2210 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2210 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2210_checked : acceptsGraphIso
    (source (graph core2210) (root 8) 0 4) DegreeTwoThreeSpectrum3638.graph sourceMap2210=true := by decide +kernel
theorem fusedMap2210_checked : acceptsGraphIso
    (fused (graph core2210) (root 8) 0 4) DegreeTwoThreeSpectrum2826.graph fusedMap2210=true := by decide +kernel
theorem certified2210 : Certified (graph core2210) (root 8) 0 4 :=
  of_native_maps core2210 DegreeTwoThreeSpectrum3638.graph DegreeTwoThreeSpectrum2826.graph
    sourceMap2210 fusedMap2210 sourceMap2210_checked fusedMap2210_checked
    DegreeTwoThreeFiniteComparisons.comparison2210
#print axioms sourceMap2210_checked
#print axioms fusedMap2210_checked
#print axioms certified2210
def sourceMap2210swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2210swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2210swap_checked : acceptsGraphIso
    (source (graph core2210) (root 8) 4 0) DegreeTwoThreeSpectrum3638.graph sourceMap2210swap=true := by decide +kernel
theorem fusedMap2210swap_checked : acceptsGraphIso
    (fused (graph core2210) (root 8) 4 0) DegreeTwoThreeSpectrum2826.graph fusedMap2210swap=true := by decide +kernel
theorem certified2210swap : Certified (graph core2210) (root 8) 4 0 :=
  of_native_maps core2210 DegreeTwoThreeSpectrum3638.graph DegreeTwoThreeSpectrum2826.graph
    sourceMap2210swap fusedMap2210swap sourceMap2210swap_checked fusedMap2210swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2210
#print axioms sourceMap2210swap_checked
#print axioms fusedMap2210swap_checked
#print axioms certified2210swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
