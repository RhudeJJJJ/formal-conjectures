/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1230 : Family 9 := level9.get ⟨154,by decide⟩
def sourceMap1230 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1230 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1230_checked : acceptsGraphIso
    (source (graph core1230) (root 9) 0 2) DegreeTwoThreeSpectrum1983.graph sourceMap1230=true := by decide +kernel
theorem fusedMap1230_checked : acceptsGraphIso
    (fused (graph core1230) (root 9) 0 2) DegreeTwoThreeSpectrum1755.graph fusedMap1230=true := by decide +kernel
theorem certified1230 : Certified (graph core1230) (root 9) 0 2 :=
  of_native_maps core1230 DegreeTwoThreeSpectrum1983.graph DegreeTwoThreeSpectrum1755.graph
    sourceMap1230 fusedMap1230 sourceMap1230_checked fusedMap1230_checked
    DegreeTwoThreeFiniteComparisons.comparison1230
#print axioms sourceMap1230_checked
#print axioms fusedMap1230_checked
#print axioms certified1230
def sourceMap1230swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1230swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1230swap_checked : acceptsGraphIso
    (source (graph core1230) (root 9) 2 0) DegreeTwoThreeSpectrum1983.graph sourceMap1230swap=true := by decide +kernel
theorem fusedMap1230swap_checked : acceptsGraphIso
    (fused (graph core1230) (root 9) 2 0) DegreeTwoThreeSpectrum1755.graph fusedMap1230swap=true := by decide +kernel
theorem certified1230swap : Certified (graph core1230) (root 9) 2 0 :=
  of_native_maps core1230 DegreeTwoThreeSpectrum1983.graph DegreeTwoThreeSpectrum1755.graph
    sourceMap1230swap fusedMap1230swap sourceMap1230swap_checked fusedMap1230swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1230
#print axioms sourceMap1230swap_checked
#print axioms fusedMap1230swap_checked
#print axioms certified1230swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
