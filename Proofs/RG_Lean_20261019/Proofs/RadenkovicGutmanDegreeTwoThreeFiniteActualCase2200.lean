/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2200 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap2200 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2200 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2200_checked : acceptsGraphIso
    (source (graph core2200) (root 8) 0 4) DegreeTwoThreeSpectrum3395.graph sourceMap2200=true := by decide +kernel
theorem fusedMap2200_checked : acceptsGraphIso
    (fused (graph core2200) (root 8) 0 4) DegreeTwoThreeSpectrum2649.graph fusedMap2200=true := by decide +kernel
theorem certified2200 : Certified (graph core2200) (root 8) 0 4 :=
  of_native_maps core2200 DegreeTwoThreeSpectrum3395.graph DegreeTwoThreeSpectrum2649.graph
    sourceMap2200 fusedMap2200 sourceMap2200_checked fusedMap2200_checked
    DegreeTwoThreeFiniteComparisons.comparison2200
#print axioms sourceMap2200_checked
#print axioms fusedMap2200_checked
#print axioms certified2200
def sourceMap2200swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2200swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2200swap_checked : acceptsGraphIso
    (source (graph core2200) (root 8) 4 0) DegreeTwoThreeSpectrum3395.graph sourceMap2200swap=true := by decide +kernel
theorem fusedMap2200swap_checked : acceptsGraphIso
    (fused (graph core2200) (root 8) 4 0) DegreeTwoThreeSpectrum2649.graph fusedMap2200swap=true := by decide +kernel
theorem certified2200swap : Certified (graph core2200) (root 8) 4 0 :=
  of_native_maps core2200 DegreeTwoThreeSpectrum3395.graph DegreeTwoThreeSpectrum2649.graph
    sourceMap2200swap fusedMap2200swap sourceMap2200swap_checked fusedMap2200swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2200
#print axioms sourceMap2200swap_checked
#print axioms fusedMap2200swap_checked
#print axioms certified2200swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
