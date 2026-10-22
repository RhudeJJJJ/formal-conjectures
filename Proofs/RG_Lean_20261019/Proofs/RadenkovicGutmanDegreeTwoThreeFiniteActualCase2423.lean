/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2423 : Family 9 := level9.get ⟨597,by decide⟩
def sourceMap2423 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2423 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2423_checked : acceptsGraphIso
    (source (graph core2423) (root 9) 0 4) DegreeTwoThreeSpectrum4730.graph sourceMap2423=true := by decide +kernel
theorem fusedMap2423_checked : acceptsGraphIso
    (fused (graph core2423) (root 9) 0 4) DegreeTwoThreeSpectrum4276.graph fusedMap2423=true := by decide +kernel
theorem certified2423 : Certified (graph core2423) (root 9) 0 4 :=
  of_native_maps core2423 DegreeTwoThreeSpectrum4730.graph DegreeTwoThreeSpectrum4276.graph
    sourceMap2423 fusedMap2423 sourceMap2423_checked fusedMap2423_checked
    DegreeTwoThreeFiniteComparisons.comparison2423
#print axioms sourceMap2423_checked
#print axioms fusedMap2423_checked
#print axioms certified2423
def sourceMap2423swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2423swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2423swap_checked : acceptsGraphIso
    (source (graph core2423) (root 9) 4 0) DegreeTwoThreeSpectrum4730.graph sourceMap2423swap=true := by decide +kernel
theorem fusedMap2423swap_checked : acceptsGraphIso
    (fused (graph core2423) (root 9) 4 0) DegreeTwoThreeSpectrum4276.graph fusedMap2423swap=true := by decide +kernel
theorem certified2423swap : Certified (graph core2423) (root 9) 4 0 :=
  of_native_maps core2423 DegreeTwoThreeSpectrum4730.graph DegreeTwoThreeSpectrum4276.graph
    sourceMap2423swap fusedMap2423swap sourceMap2423swap_checked fusedMap2423swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2423
#print axioms sourceMap2423swap_checked
#print axioms fusedMap2423swap_checked
#print axioms certified2423swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
