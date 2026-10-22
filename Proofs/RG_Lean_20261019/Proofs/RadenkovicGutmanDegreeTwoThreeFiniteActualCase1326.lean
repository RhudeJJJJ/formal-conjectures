/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1326 : Family 9 := level9.get ⟨423,by decide⟩
def sourceMap1326 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1326 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1326_checked : acceptsGraphIso
    (source (graph core1326) (root 9) 0 2) DegreeTwoThreeSpectrum2090.graph sourceMap1326=true := by decide +kernel
theorem fusedMap1326_checked : acceptsGraphIso
    (fused (graph core1326) (root 9) 0 2) DegreeTwoThreeSpectrum2091.graph fusedMap1326=true := by decide +kernel
theorem certified1326 : Certified (graph core1326) (root 9) 0 2 :=
  of_native_maps core1326 DegreeTwoThreeSpectrum2090.graph DegreeTwoThreeSpectrum2091.graph
    sourceMap1326 fusedMap1326 sourceMap1326_checked fusedMap1326_checked
    DegreeTwoThreeFiniteComparisons.comparison1326
#print axioms sourceMap1326_checked
#print axioms fusedMap1326_checked
#print axioms certified1326
def sourceMap1326swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1326swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1326swap_checked : acceptsGraphIso
    (source (graph core1326) (root 9) 2 0) DegreeTwoThreeSpectrum2090.graph sourceMap1326swap=true := by decide +kernel
theorem fusedMap1326swap_checked : acceptsGraphIso
    (fused (graph core1326) (root 9) 2 0) DegreeTwoThreeSpectrum2091.graph fusedMap1326swap=true := by decide +kernel
theorem certified1326swap : Certified (graph core1326) (root 9) 2 0 :=
  of_native_maps core1326 DegreeTwoThreeSpectrum2090.graph DegreeTwoThreeSpectrum2091.graph
    sourceMap1326swap fusedMap1326swap sourceMap1326swap_checked fusedMap1326swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1326
#print axioms sourceMap1326swap_checked
#print axioms fusedMap1326swap_checked
#print axioms certified1326swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
