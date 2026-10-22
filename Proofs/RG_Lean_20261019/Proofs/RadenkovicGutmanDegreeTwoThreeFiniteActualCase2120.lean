/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2120 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap2120 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2120 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 0 4 v)
theorem sourceMap2120_checked : acceptsGraphIso
    (source (graph core2120) (root 8) 0 4) DegreeTwoThreeSpectrum2347.graph sourceMap2120=true := by decide +kernel
theorem fusedMap2120_checked : acceptsGraphIso
    (fused (graph core2120) (root 8) 0 4) DegreeTwoThreeSpectrum2348.graph fusedMap2120=true := by decide +kernel
theorem certified2120 : Certified (graph core2120) (root 8) 0 4 :=
  of_native_maps core2120 DegreeTwoThreeSpectrum2347.graph DegreeTwoThreeSpectrum2348.graph
    sourceMap2120 fusedMap2120 sourceMap2120_checked fusedMap2120_checked
    DegreeTwoThreeFiniteComparisons.comparison2120
#print axioms sourceMap2120_checked
#print axioms fusedMap2120_checked
#print axioms certified2120
def sourceMap2120swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2120swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 4 0 v)
theorem sourceMap2120swap_checked : acceptsGraphIso
    (source (graph core2120) (root 8) 4 0) DegreeTwoThreeSpectrum2347.graph sourceMap2120swap=true := by decide +kernel
theorem fusedMap2120swap_checked : acceptsGraphIso
    (fused (graph core2120) (root 8) 4 0) DegreeTwoThreeSpectrum2348.graph fusedMap2120swap=true := by decide +kernel
theorem certified2120swap : Certified (graph core2120) (root 8) 4 0 :=
  of_native_maps core2120 DegreeTwoThreeSpectrum2347.graph DegreeTwoThreeSpectrum2348.graph
    sourceMap2120swap fusedMap2120swap sourceMap2120swap_checked fusedMap2120swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2120
#print axioms sourceMap2120swap_checked
#print axioms fusedMap2120swap_checked
#print axioms certified2120swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
