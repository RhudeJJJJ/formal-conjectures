/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3393 : Family 9 := level9.get ⟨477,by decide⟩
def sourceMap3393 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3393 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3393_checked : acceptsGraphIso
    (source (graph core3393) (root 9) 0 5) DegreeTwoThreeSpectrum6751.graph sourceMap3393=true := by decide +kernel
theorem fusedMap3393_checked : acceptsGraphIso
    (fused (graph core3393) (root 9) 0 5) DegreeTwoThreeSpectrum5596.graph fusedMap3393=true := by decide +kernel
theorem certified3393 : Certified (graph core3393) (root 9) 0 5 :=
  of_native_maps core3393 DegreeTwoThreeSpectrum6751.graph DegreeTwoThreeSpectrum5596.graph
    sourceMap3393 fusedMap3393 sourceMap3393_checked fusedMap3393_checked
    DegreeTwoThreeFiniteComparisons.comparison3393
#print axioms sourceMap3393_checked
#print axioms fusedMap3393_checked
#print axioms certified3393
def sourceMap3393swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3393swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3393swap_checked : acceptsGraphIso
    (source (graph core3393) (root 9) 5 0) DegreeTwoThreeSpectrum6751.graph sourceMap3393swap=true := by decide +kernel
theorem fusedMap3393swap_checked : acceptsGraphIso
    (fused (graph core3393) (root 9) 5 0) DegreeTwoThreeSpectrum5596.graph fusedMap3393swap=true := by decide +kernel
theorem certified3393swap : Certified (graph core3393) (root 9) 5 0 :=
  of_native_maps core3393 DegreeTwoThreeSpectrum6751.graph DegreeTwoThreeSpectrum5596.graph
    sourceMap3393swap fusedMap3393swap sourceMap3393swap_checked fusedMap3393swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3393
#print axioms sourceMap3393swap_checked
#print axioms fusedMap3393swap_checked
#print axioms certified3393swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
