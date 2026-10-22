/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3356 : Family 9 := level9.get ⟨389,by decide⟩
def sourceMap3356 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3356 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3356_checked : acceptsGraphIso
    (source (graph core3356) (root 9) 0 5) DegreeTwoThreeSpectrum6354.graph sourceMap3356=true := by decide +kernel
theorem fusedMap3356_checked : acceptsGraphIso
    (fused (graph core3356) (root 9) 0 5) DegreeTwoThreeSpectrum5308.graph fusedMap3356=true := by decide +kernel
theorem certified3356 : Certified (graph core3356) (root 9) 0 5 :=
  of_native_maps core3356 DegreeTwoThreeSpectrum6354.graph DegreeTwoThreeSpectrum5308.graph
    sourceMap3356 fusedMap3356 sourceMap3356_checked fusedMap3356_checked
    DegreeTwoThreeFiniteComparisons.comparison3356
#print axioms sourceMap3356_checked
#print axioms fusedMap3356_checked
#print axioms certified3356
def sourceMap3356swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3356swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3356swap_checked : acceptsGraphIso
    (source (graph core3356) (root 9) 5 0) DegreeTwoThreeSpectrum6354.graph sourceMap3356swap=true := by decide +kernel
theorem fusedMap3356swap_checked : acceptsGraphIso
    (fused (graph core3356) (root 9) 5 0) DegreeTwoThreeSpectrum5308.graph fusedMap3356swap=true := by decide +kernel
theorem certified3356swap : Certified (graph core3356) (root 9) 5 0 :=
  of_native_maps core3356 DegreeTwoThreeSpectrum6354.graph DegreeTwoThreeSpectrum5308.graph
    sourceMap3356swap fusedMap3356swap sourceMap3356swap_checked fusedMap3356swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3356
#print axioms sourceMap3356swap_checked
#print axioms fusedMap3356swap_checked
#print axioms certified3356swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
