/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3351 : Family 9 := level9.get ⟨377,by decide⟩
def sourceMap3351 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3351 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3351_checked : acceptsGraphIso
    (source (graph core3351) (root 9) 0 5) DegreeTwoThreeSpectrum6299.graph sourceMap3351=true := by decide +kernel
theorem fusedMap3351_checked : acceptsGraphIso
    (fused (graph core3351) (root 9) 0 5) DegreeTwoThreeSpectrum5267.graph fusedMap3351=true := by decide +kernel
theorem certified3351 : Certified (graph core3351) (root 9) 0 5 :=
  of_native_maps core3351 DegreeTwoThreeSpectrum6299.graph DegreeTwoThreeSpectrum5267.graph
    sourceMap3351 fusedMap3351 sourceMap3351_checked fusedMap3351_checked
    DegreeTwoThreeFiniteComparisons.comparison3351
#print axioms sourceMap3351_checked
#print axioms fusedMap3351_checked
#print axioms certified3351
def sourceMap3351swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3351swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3351swap_checked : acceptsGraphIso
    (source (graph core3351) (root 9) 5 0) DegreeTwoThreeSpectrum6299.graph sourceMap3351swap=true := by decide +kernel
theorem fusedMap3351swap_checked : acceptsGraphIso
    (fused (graph core3351) (root 9) 5 0) DegreeTwoThreeSpectrum5267.graph fusedMap3351swap=true := by decide +kernel
theorem certified3351swap : Certified (graph core3351) (root 9) 5 0 :=
  of_native_maps core3351 DegreeTwoThreeSpectrum6299.graph DegreeTwoThreeSpectrum5267.graph
    sourceMap3351swap fusedMap3351swap sourceMap3351swap_checked fusedMap3351swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3351
#print axioms sourceMap3351swap_checked
#print axioms fusedMap3351swap_checked
#print axioms certified3351swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
