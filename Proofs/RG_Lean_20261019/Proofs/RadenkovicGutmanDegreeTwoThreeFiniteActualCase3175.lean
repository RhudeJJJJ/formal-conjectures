/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3175 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap3175 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3175 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3175_checked : acceptsGraphIso
    (source (graph core3175) (root 8) 0 5) DegreeTwoThreeSpectrum4357.graph sourceMap3175=true := by decide +kernel
theorem fusedMap3175_checked : acceptsGraphIso
    (fused (graph core3175) (root 8) 0 5) DegreeTwoThreeSpectrum3947.graph fusedMap3175=true := by decide +kernel
theorem certified3175 : Certified (graph core3175) (root 8) 0 5 :=
  of_native_maps core3175 DegreeTwoThreeSpectrum4357.graph DegreeTwoThreeSpectrum3947.graph
    sourceMap3175 fusedMap3175 sourceMap3175_checked fusedMap3175_checked
    DegreeTwoThreeFiniteComparisons.comparison3175
#print axioms sourceMap3175_checked
#print axioms fusedMap3175_checked
#print axioms certified3175
def sourceMap3175swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3175swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3175swap_checked : acceptsGraphIso
    (source (graph core3175) (root 8) 5 0) DegreeTwoThreeSpectrum4357.graph sourceMap3175swap=true := by decide +kernel
theorem fusedMap3175swap_checked : acceptsGraphIso
    (fused (graph core3175) (root 8) 5 0) DegreeTwoThreeSpectrum3947.graph fusedMap3175swap=true := by decide +kernel
theorem certified3175swap : Certified (graph core3175) (root 8) 5 0 :=
  of_native_maps core3175 DegreeTwoThreeSpectrum4357.graph DegreeTwoThreeSpectrum3947.graph
    sourceMap3175swap fusedMap3175swap sourceMap3175swap_checked fusedMap3175swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3175
#print axioms sourceMap3175swap_checked
#print axioms fusedMap3175swap_checked
#print axioms certified3175swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
