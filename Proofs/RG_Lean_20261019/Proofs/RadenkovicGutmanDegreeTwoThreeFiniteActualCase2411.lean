/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2411 : Family 9 := level9.get ⟨571,by decide⟩
def sourceMap2411 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2411 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2411_checked : acceptsGraphIso
    (source (graph core2411) (root 9) 0 4) DegreeTwoThreeSpectrum4700.graph sourceMap2411=true := by decide +kernel
theorem fusedMap2411_checked : acceptsGraphIso
    (fused (graph core2411) (root 9) 0 4) DegreeTwoThreeSpectrum4217.graph fusedMap2411=true := by decide +kernel
theorem certified2411 : Certified (graph core2411) (root 9) 0 4 :=
  of_native_maps core2411 DegreeTwoThreeSpectrum4700.graph DegreeTwoThreeSpectrum4217.graph
    sourceMap2411 fusedMap2411 sourceMap2411_checked fusedMap2411_checked
    DegreeTwoThreeFiniteComparisons.comparison2411
#print axioms sourceMap2411_checked
#print axioms fusedMap2411_checked
#print axioms certified2411
def sourceMap2411swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2411swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2411swap_checked : acceptsGraphIso
    (source (graph core2411) (root 9) 4 0) DegreeTwoThreeSpectrum4700.graph sourceMap2411swap=true := by decide +kernel
theorem fusedMap2411swap_checked : acceptsGraphIso
    (fused (graph core2411) (root 9) 4 0) DegreeTwoThreeSpectrum4217.graph fusedMap2411swap=true := by decide +kernel
theorem certified2411swap : Certified (graph core2411) (root 9) 4 0 :=
  of_native_maps core2411 DegreeTwoThreeSpectrum4700.graph DegreeTwoThreeSpectrum4217.graph
    sourceMap2411swap fusedMap2411swap sourceMap2411swap_checked fusedMap2411swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2411
#print axioms sourceMap2411swap_checked
#print axioms fusedMap2411swap_checked
#print axioms certified2411swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
