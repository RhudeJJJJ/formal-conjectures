/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2427 : Family 9 := level9.get ⟨605,by decide⟩
def sourceMap2427 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2427 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2427_checked : acceptsGraphIso
    (source (graph core2427) (root 9) 0 4) DegreeTwoThreeSpectrum4739.graph sourceMap2427=true := by decide +kernel
theorem fusedMap2427_checked : acceptsGraphIso
    (fused (graph core2427) (root 9) 0 4) DegreeTwoThreeSpectrum4293.graph fusedMap2427=true := by decide +kernel
theorem certified2427 : Certified (graph core2427) (root 9) 0 4 :=
  of_native_maps core2427 DegreeTwoThreeSpectrum4739.graph DegreeTwoThreeSpectrum4293.graph
    sourceMap2427 fusedMap2427 sourceMap2427_checked fusedMap2427_checked
    DegreeTwoThreeFiniteComparisons.comparison2427
#print axioms sourceMap2427_checked
#print axioms fusedMap2427_checked
#print axioms certified2427
def sourceMap2427swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2427swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2427swap_checked : acceptsGraphIso
    (source (graph core2427) (root 9) 4 0) DegreeTwoThreeSpectrum4739.graph sourceMap2427swap=true := by decide +kernel
theorem fusedMap2427swap_checked : acceptsGraphIso
    (fused (graph core2427) (root 9) 4 0) DegreeTwoThreeSpectrum4293.graph fusedMap2427swap=true := by decide +kernel
theorem certified2427swap : Certified (graph core2427) (root 9) 4 0 :=
  of_native_maps core2427 DegreeTwoThreeSpectrum4739.graph DegreeTwoThreeSpectrum4293.graph
    sourceMap2427swap fusedMap2427swap sourceMap2427swap_checked fusedMap2427swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2427
#print axioms sourceMap2427swap_checked
#print axioms fusedMap2427swap_checked
#print axioms certified2427swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
