/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2217 : Family 9 := level9.get ⟨22,by decide⟩
def sourceMap2217 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2217 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2217_checked : acceptsGraphIso
    (source (graph core2217) (root 9) 0 4) DegreeTwoThreeSpectrum4056.graph sourceMap2217=true := by decide +kernel
theorem fusedMap2217_checked : acceptsGraphIso
    (fused (graph core2217) (root 9) 0 4) DegreeTwoThreeSpectrum3868.graph fusedMap2217=true := by decide +kernel
theorem certified2217 : Certified (graph core2217) (root 9) 0 4 :=
  of_native_maps core2217 DegreeTwoThreeSpectrum4056.graph DegreeTwoThreeSpectrum3868.graph
    sourceMap2217 fusedMap2217 sourceMap2217_checked fusedMap2217_checked
    DegreeTwoThreeFiniteComparisons.comparison2217
#print axioms sourceMap2217_checked
#print axioms fusedMap2217_checked
#print axioms certified2217
def sourceMap2217swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2217swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2217swap_checked : acceptsGraphIso
    (source (graph core2217) (root 9) 4 0) DegreeTwoThreeSpectrum4056.graph sourceMap2217swap=true := by decide +kernel
theorem fusedMap2217swap_checked : acceptsGraphIso
    (fused (graph core2217) (root 9) 4 0) DegreeTwoThreeSpectrum3868.graph fusedMap2217swap=true := by decide +kernel
theorem certified2217swap : Certified (graph core2217) (root 9) 4 0 :=
  of_native_maps core2217 DegreeTwoThreeSpectrum4056.graph DegreeTwoThreeSpectrum3868.graph
    sourceMap2217swap fusedMap2217swap sourceMap2217swap_checked fusedMap2217swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2217
#print axioms sourceMap2217swap_checked
#print axioms fusedMap2217swap_checked
#print axioms certified2217swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
