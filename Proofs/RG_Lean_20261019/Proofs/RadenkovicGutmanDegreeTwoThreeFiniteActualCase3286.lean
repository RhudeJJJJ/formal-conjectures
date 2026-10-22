/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3286 : Family 9 := level9.get ⟨193,by decide⟩
def sourceMap3286 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3286 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3286_checked : acceptsGraphIso
    (source (graph core3286) (root 9) 0 5) DegreeTwoThreeSpectrum5387.graph sourceMap3286=true := by decide +kernel
theorem fusedMap3286_checked : acceptsGraphIso
    (fused (graph core3286) (root 9) 0 5) DegreeTwoThreeSpectrum5388.graph fusedMap3286=true := by decide +kernel
theorem certified3286 : Certified (graph core3286) (root 9) 0 5 :=
  of_native_maps core3286 DegreeTwoThreeSpectrum5387.graph DegreeTwoThreeSpectrum5388.graph
    sourceMap3286 fusedMap3286 sourceMap3286_checked fusedMap3286_checked
    DegreeTwoThreeFiniteComparisons.comparison3286
#print axioms sourceMap3286_checked
#print axioms fusedMap3286_checked
#print axioms certified3286
def sourceMap3286swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3286swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3286swap_checked : acceptsGraphIso
    (source (graph core3286) (root 9) 5 0) DegreeTwoThreeSpectrum5387.graph sourceMap3286swap=true := by decide +kernel
theorem fusedMap3286swap_checked : acceptsGraphIso
    (fused (graph core3286) (root 9) 5 0) DegreeTwoThreeSpectrum5388.graph fusedMap3286swap=true := by decide +kernel
theorem certified3286swap : Certified (graph core3286) (root 9) 5 0 :=
  of_native_maps core3286 DegreeTwoThreeSpectrum5387.graph DegreeTwoThreeSpectrum5388.graph
    sourceMap3286swap fusedMap3286swap sourceMap3286swap_checked fusedMap3286swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3286
#print axioms sourceMap3286swap_checked
#print axioms fusedMap3286swap_checked
#print axioms certified3286swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
