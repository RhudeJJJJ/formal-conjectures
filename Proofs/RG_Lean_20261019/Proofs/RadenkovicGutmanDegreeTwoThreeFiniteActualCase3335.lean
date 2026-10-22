/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3335 : Family 9 := level9.get ⟨333,by decide⟩
def sourceMap3335 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3335 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3335_checked : acceptsGraphIso
    (source (graph core3335) (root 9) 0 5) DegreeTwoThreeSpectrum6071.graph sourceMap3335=true := by decide +kernel
theorem fusedMap3335_checked : acceptsGraphIso
    (fused (graph core3335) (root 9) 0 5) DegreeTwoThreeSpectrum5162.graph fusedMap3335=true := by decide +kernel
theorem certified3335 : Certified (graph core3335) (root 9) 0 5 :=
  of_native_maps core3335 DegreeTwoThreeSpectrum6071.graph DegreeTwoThreeSpectrum5162.graph
    sourceMap3335 fusedMap3335 sourceMap3335_checked fusedMap3335_checked
    DegreeTwoThreeFiniteComparisons.comparison3335
#print axioms sourceMap3335_checked
#print axioms fusedMap3335_checked
#print axioms certified3335
def sourceMap3335swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3335swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3335swap_checked : acceptsGraphIso
    (source (graph core3335) (root 9) 5 0) DegreeTwoThreeSpectrum6071.graph sourceMap3335swap=true := by decide +kernel
theorem fusedMap3335swap_checked : acceptsGraphIso
    (fused (graph core3335) (root 9) 5 0) DegreeTwoThreeSpectrum5162.graph fusedMap3335swap=true := by decide +kernel
theorem certified3335swap : Certified (graph core3335) (root 9) 5 0 :=
  of_native_maps core3335 DegreeTwoThreeSpectrum6071.graph DegreeTwoThreeSpectrum5162.graph
    sourceMap3335swap fusedMap3335swap sourceMap3335swap_checked fusedMap3335swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3335
#print axioms sourceMap3335swap_checked
#print axioms fusedMap3335swap_checked
#print axioms certified3335swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
