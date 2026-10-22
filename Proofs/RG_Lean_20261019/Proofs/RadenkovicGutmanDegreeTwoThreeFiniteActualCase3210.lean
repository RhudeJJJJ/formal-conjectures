/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3210 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap3210 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3210 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3210_checked : acceptsGraphIso
    (source (graph core3210) (root 8) 0 5) DegreeTwoThreeSpectrum4263.graph sourceMap3210=true := by decide +kernel
theorem fusedMap3210_checked : acceptsGraphIso
    (fused (graph core3210) (root 8) 0 5) DegreeTwoThreeSpectrum4264.graph fusedMap3210=true := by decide +kernel
theorem certified3210 : Certified (graph core3210) (root 8) 0 5 :=
  of_native_maps core3210 DegreeTwoThreeSpectrum4263.graph DegreeTwoThreeSpectrum4264.graph
    sourceMap3210 fusedMap3210 sourceMap3210_checked fusedMap3210_checked
    DegreeTwoThreeFiniteComparisons.comparison3210
#print axioms sourceMap3210_checked
#print axioms fusedMap3210_checked
#print axioms certified3210
def sourceMap3210swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3210swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3210swap_checked : acceptsGraphIso
    (source (graph core3210) (root 8) 5 0) DegreeTwoThreeSpectrum4263.graph sourceMap3210swap=true := by decide +kernel
theorem fusedMap3210swap_checked : acceptsGraphIso
    (fused (graph core3210) (root 8) 5 0) DegreeTwoThreeSpectrum4264.graph fusedMap3210swap=true := by decide +kernel
theorem certified3210swap : Certified (graph core3210) (root 8) 5 0 :=
  of_native_maps core3210 DegreeTwoThreeSpectrum4263.graph DegreeTwoThreeSpectrum4264.graph
    sourceMap3210swap fusedMap3210swap sourceMap3210swap_checked fusedMap3210swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3210
#print axioms sourceMap3210swap_checked
#print axioms fusedMap3210swap_checked
#print axioms certified3210swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
