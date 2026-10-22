/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3399 : Family 9 := level9.get ⟨493,by decide⟩
def sourceMap3399 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3399 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3399_checked : acceptsGraphIso
    (source (graph core3399) (root 9) 0 5) DegreeTwoThreeSpectrum6878.graph sourceMap3399=true := by decide +kernel
theorem fusedMap3399_checked : acceptsGraphIso
    (fused (graph core3399) (root 9) 0 5) DegreeTwoThreeSpectrum5673.graph fusedMap3399=true := by decide +kernel
theorem certified3399 : Certified (graph core3399) (root 9) 0 5 :=
  of_native_maps core3399 DegreeTwoThreeSpectrum6878.graph DegreeTwoThreeSpectrum5673.graph
    sourceMap3399 fusedMap3399 sourceMap3399_checked fusedMap3399_checked
    DegreeTwoThreeFiniteComparisons.comparison3399
#print axioms sourceMap3399_checked
#print axioms fusedMap3399_checked
#print axioms certified3399
def sourceMap3399swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3399swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3399swap_checked : acceptsGraphIso
    (source (graph core3399) (root 9) 5 0) DegreeTwoThreeSpectrum6878.graph sourceMap3399swap=true := by decide +kernel
theorem fusedMap3399swap_checked : acceptsGraphIso
    (fused (graph core3399) (root 9) 5 0) DegreeTwoThreeSpectrum5673.graph fusedMap3399swap=true := by decide +kernel
theorem certified3399swap : Certified (graph core3399) (root 9) 5 0 :=
  of_native_maps core3399 DegreeTwoThreeSpectrum6878.graph DegreeTwoThreeSpectrum5673.graph
    sourceMap3399swap fusedMap3399swap sourceMap3399swap_checked fusedMap3399swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3399
#print axioms sourceMap3399swap_checked
#print axioms fusedMap3399swap_checked
#print axioms certified3399swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
