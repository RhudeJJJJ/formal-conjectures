/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3258 : Family 9 := level9.get ⟨106,by decide⟩
def sourceMap3258 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3258 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3258_checked : acceptsGraphIso
    (source (graph core3258) (root 9) 0 5) DegreeTwoThreeSpectrum5793.graph sourceMap3258=true := by decide +kernel
theorem fusedMap3258_checked : acceptsGraphIso
    (fused (graph core3258) (root 9) 0 5) DegreeTwoThreeSpectrum5064.graph fusedMap3258=true := by decide +kernel
theorem certified3258 : Certified (graph core3258) (root 9) 0 5 :=
  of_native_maps core3258 DegreeTwoThreeSpectrum5793.graph DegreeTwoThreeSpectrum5064.graph
    sourceMap3258 fusedMap3258 sourceMap3258_checked fusedMap3258_checked
    DegreeTwoThreeFiniteComparisons.comparison3258
#print axioms sourceMap3258_checked
#print axioms fusedMap3258_checked
#print axioms certified3258
def sourceMap3258swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3258swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3258swap_checked : acceptsGraphIso
    (source (graph core3258) (root 9) 5 0) DegreeTwoThreeSpectrum5793.graph sourceMap3258swap=true := by decide +kernel
theorem fusedMap3258swap_checked : acceptsGraphIso
    (fused (graph core3258) (root 9) 5 0) DegreeTwoThreeSpectrum5064.graph fusedMap3258swap=true := by decide +kernel
theorem certified3258swap : Certified (graph core3258) (root 9) 5 0 :=
  of_native_maps core3258 DegreeTwoThreeSpectrum5793.graph DegreeTwoThreeSpectrum5064.graph
    sourceMap3258swap fusedMap3258swap sourceMap3258swap_checked fusedMap3258swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3258
#print axioms sourceMap3258swap_checked
#print axioms fusedMap3258swap_checked
#print axioms certified3258swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
