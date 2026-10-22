/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3143 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap3143 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 8 0 5 v)
def fusedMap3143 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3143_checked : acceptsGraphIso
    (source (graph core3143) (root 8) 0 5) DegreeTwoThreeSpectrum4114.graph sourceMap3143=true := by decide +kernel
theorem fusedMap3143_checked : acceptsGraphIso
    (fused (graph core3143) (root 8) 0 5) DegreeTwoThreeSpectrum3874.graph fusedMap3143=true := by decide +kernel
theorem certified3143 : Certified (graph core3143) (root 8) 0 5 :=
  of_native_maps core3143 DegreeTwoThreeSpectrum4114.graph DegreeTwoThreeSpectrum3874.graph
    sourceMap3143 fusedMap3143 sourceMap3143_checked fusedMap3143_checked
    DegreeTwoThreeFiniteComparisons.comparison3143
#print axioms sourceMap3143_checked
#print axioms fusedMap3143_checked
#print axioms certified3143
def sourceMap3143swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13,15] (sourceLabel 8 5 0 v)
def fusedMap3143swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3143swap_checked : acceptsGraphIso
    (source (graph core3143) (root 8) 5 0) DegreeTwoThreeSpectrum4114.graph sourceMap3143swap=true := by decide +kernel
theorem fusedMap3143swap_checked : acceptsGraphIso
    (fused (graph core3143) (root 8) 5 0) DegreeTwoThreeSpectrum3874.graph fusedMap3143swap=true := by decide +kernel
theorem certified3143swap : Certified (graph core3143) (root 8) 5 0 :=
  of_native_maps core3143 DegreeTwoThreeSpectrum4114.graph DegreeTwoThreeSpectrum3874.graph
    sourceMap3143swap fusedMap3143swap sourceMap3143swap_checked fusedMap3143swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3143
#print axioms sourceMap3143swap_checked
#print axioms fusedMap3143swap_checked
#print axioms certified3143swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
