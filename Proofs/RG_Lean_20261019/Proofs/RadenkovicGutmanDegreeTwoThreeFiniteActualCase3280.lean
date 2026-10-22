/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3280 : Family 9 := level9.get ⟨178,by decide⟩
def sourceMap3280 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3280 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3280_checked : acceptsGraphIso
    (source (graph core3280) (root 9) 0 5) DegreeTwoThreeSpectrum5324.graph sourceMap3280=true := by decide +kernel
theorem fusedMap3280_checked : acceptsGraphIso
    (fused (graph core3280) (root 9) 0 5) DegreeTwoThreeSpectrum5325.graph fusedMap3280=true := by decide +kernel
theorem certified3280 : Certified (graph core3280) (root 9) 0 5 :=
  of_native_maps core3280 DegreeTwoThreeSpectrum5324.graph DegreeTwoThreeSpectrum5325.graph
    sourceMap3280 fusedMap3280 sourceMap3280_checked fusedMap3280_checked
    DegreeTwoThreeFiniteComparisons.comparison3280
#print axioms sourceMap3280_checked
#print axioms fusedMap3280_checked
#print axioms certified3280
def sourceMap3280swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3280swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3280swap_checked : acceptsGraphIso
    (source (graph core3280) (root 9) 5 0) DegreeTwoThreeSpectrum5324.graph sourceMap3280swap=true := by decide +kernel
theorem fusedMap3280swap_checked : acceptsGraphIso
    (fused (graph core3280) (root 9) 5 0) DegreeTwoThreeSpectrum5325.graph fusedMap3280swap=true := by decide +kernel
theorem certified3280swap : Certified (graph core3280) (root 9) 5 0 :=
  of_native_maps core3280 DegreeTwoThreeSpectrum5324.graph DegreeTwoThreeSpectrum5325.graph
    sourceMap3280swap fusedMap3280swap sourceMap3280swap_checked fusedMap3280swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3280
#print axioms sourceMap3280swap_checked
#print axioms fusedMap3280swap_checked
#print axioms certified3280swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
