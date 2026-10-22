/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3346 : Family 9 := level9.get ⟨363,by decide⟩
def sourceMap3346 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3346 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3346_checked : acceptsGraphIso
    (source (graph core3346) (root 9) 0 5) DegreeTwoThreeSpectrum6227.graph sourceMap3346=true := by decide +kernel
theorem fusedMap3346_checked : acceptsGraphIso
    (fused (graph core3346) (root 9) 0 5) DegreeTwoThreeSpectrum5235.graph fusedMap3346=true := by decide +kernel
theorem certified3346 : Certified (graph core3346) (root 9) 0 5 :=
  of_native_maps core3346 DegreeTwoThreeSpectrum6227.graph DegreeTwoThreeSpectrum5235.graph
    sourceMap3346 fusedMap3346 sourceMap3346_checked fusedMap3346_checked
    DegreeTwoThreeFiniteComparisons.comparison3346
#print axioms sourceMap3346_checked
#print axioms fusedMap3346_checked
#print axioms certified3346
def sourceMap3346swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3346swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3346swap_checked : acceptsGraphIso
    (source (graph core3346) (root 9) 5 0) DegreeTwoThreeSpectrum6227.graph sourceMap3346swap=true := by decide +kernel
theorem fusedMap3346swap_checked : acceptsGraphIso
    (fused (graph core3346) (root 9) 5 0) DegreeTwoThreeSpectrum5235.graph fusedMap3346swap=true := by decide +kernel
theorem certified3346swap : Certified (graph core3346) (root 9) 5 0 :=
  of_native_maps core3346 DegreeTwoThreeSpectrum6227.graph DegreeTwoThreeSpectrum5235.graph
    sourceMap3346swap fusedMap3346swap sourceMap3346swap_checked fusedMap3346swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3346
#print axioms sourceMap3346swap_checked
#print axioms fusedMap3346swap_checked
#print axioms certified3346swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
