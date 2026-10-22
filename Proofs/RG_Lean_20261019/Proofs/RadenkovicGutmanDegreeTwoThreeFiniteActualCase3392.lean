/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3392 : Family 9 := level9.get ⟨474,by decide⟩
def sourceMap3392 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3392 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3392_checked : acceptsGraphIso
    (source (graph core3392) (root 9) 0 5) DegreeTwoThreeSpectrum6737.graph sourceMap3392=true := by decide +kernel
theorem fusedMap3392_checked : acceptsGraphIso
    (fused (graph core3392) (root 9) 0 5) DegreeTwoThreeSpectrum5574.graph fusedMap3392=true := by decide +kernel
theorem certified3392 : Certified (graph core3392) (root 9) 0 5 :=
  of_native_maps core3392 DegreeTwoThreeSpectrum6737.graph DegreeTwoThreeSpectrum5574.graph
    sourceMap3392 fusedMap3392 sourceMap3392_checked fusedMap3392_checked
    DegreeTwoThreeFiniteComparisons.comparison3392
#print axioms sourceMap3392_checked
#print axioms fusedMap3392_checked
#print axioms certified3392
def sourceMap3392swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3392swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3392swap_checked : acceptsGraphIso
    (source (graph core3392) (root 9) 5 0) DegreeTwoThreeSpectrum6737.graph sourceMap3392swap=true := by decide +kernel
theorem fusedMap3392swap_checked : acceptsGraphIso
    (fused (graph core3392) (root 9) 5 0) DegreeTwoThreeSpectrum5574.graph fusedMap3392swap=true := by decide +kernel
theorem certified3392swap : Certified (graph core3392) (root 9) 5 0 :=
  of_native_maps core3392 DegreeTwoThreeSpectrum6737.graph DegreeTwoThreeSpectrum5574.graph
    sourceMap3392swap fusedMap3392swap sourceMap3392swap_checked fusedMap3392swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3392
#print axioms sourceMap3392swap_checked
#print axioms fusedMap3392swap_checked
#print axioms certified3392swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
