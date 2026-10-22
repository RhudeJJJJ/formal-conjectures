/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3299 : Family 9 := level9.get ⟨236,by decide⟩
def sourceMap3299 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3299 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3299_checked : acceptsGraphIso
    (source (graph core3299) (root 9) 0 5) DegreeTwoThreeSpectrum5581.graph sourceMap3299=true := by decide +kernel
theorem fusedMap3299_checked : acceptsGraphIso
    (fused (graph core3299) (root 9) 0 5) DegreeTwoThreeSpectrum5582.graph fusedMap3299=true := by decide +kernel
theorem certified3299 : Certified (graph core3299) (root 9) 0 5 :=
  of_native_maps core3299 DegreeTwoThreeSpectrum5581.graph DegreeTwoThreeSpectrum5582.graph
    sourceMap3299 fusedMap3299 sourceMap3299_checked fusedMap3299_checked
    DegreeTwoThreeFiniteComparisons.comparison3299
#print axioms sourceMap3299_checked
#print axioms fusedMap3299_checked
#print axioms certified3299
def sourceMap3299swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3299swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3299swap_checked : acceptsGraphIso
    (source (graph core3299) (root 9) 5 0) DegreeTwoThreeSpectrum5581.graph sourceMap3299swap=true := by decide +kernel
theorem fusedMap3299swap_checked : acceptsGraphIso
    (fused (graph core3299) (root 9) 5 0) DegreeTwoThreeSpectrum5582.graph fusedMap3299swap=true := by decide +kernel
theorem certified3299swap : Certified (graph core3299) (root 9) 5 0 :=
  of_native_maps core3299 DegreeTwoThreeSpectrum5581.graph DegreeTwoThreeSpectrum5582.graph
    sourceMap3299swap fusedMap3299swap sourceMap3299swap_checked fusedMap3299swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3299
#print axioms sourceMap3299swap_checked
#print axioms fusedMap3299swap_checked
#print axioms certified3299swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
