/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3326 : Family 9 := level9.get ⟨305,by decide⟩
def sourceMap3326 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3326 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3326_checked : acceptsGraphIso
    (source (graph core3326) (root 9) 0 5) DegreeTwoThreeSpectrum5891.graph sourceMap3326=true := by decide +kernel
theorem fusedMap3326_checked : acceptsGraphIso
    (fused (graph core3326) (root 9) 0 5) DegreeTwoThreeSpectrum5892.graph fusedMap3326=true := by decide +kernel
theorem certified3326 : Certified (graph core3326) (root 9) 0 5 :=
  of_native_maps core3326 DegreeTwoThreeSpectrum5891.graph DegreeTwoThreeSpectrum5892.graph
    sourceMap3326 fusedMap3326 sourceMap3326_checked fusedMap3326_checked
    DegreeTwoThreeFiniteComparisons.comparison3326
#print axioms sourceMap3326_checked
#print axioms fusedMap3326_checked
#print axioms certified3326
def sourceMap3326swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3326swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3326swap_checked : acceptsGraphIso
    (source (graph core3326) (root 9) 5 0) DegreeTwoThreeSpectrum5891.graph sourceMap3326swap=true := by decide +kernel
theorem fusedMap3326swap_checked : acceptsGraphIso
    (fused (graph core3326) (root 9) 5 0) DegreeTwoThreeSpectrum5892.graph fusedMap3326swap=true := by decide +kernel
theorem certified3326swap : Certified (graph core3326) (root 9) 5 0 :=
  of_native_maps core3326 DegreeTwoThreeSpectrum5891.graph DegreeTwoThreeSpectrum5892.graph
    sourceMap3326swap fusedMap3326swap sourceMap3326swap_checked fusedMap3326swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3326
#print axioms sourceMap3326swap_checked
#print axioms fusedMap3326swap_checked
#print axioms certified3326swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
