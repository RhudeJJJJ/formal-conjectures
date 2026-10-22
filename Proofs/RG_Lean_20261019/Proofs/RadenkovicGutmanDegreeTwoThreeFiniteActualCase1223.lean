/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1223 : Family 9 := level9.get ⟨131,by decide⟩
def sourceMap1223 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,8,5,6,7,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1223 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,6,7,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1223_checked : acceptsGraphIso
    (source (graph core1223) (root 9) 0 2) DegreeTwoThreeSpectrum1867.graph sourceMap1223=true := by decide +kernel
theorem fusedMap1223_checked : acceptsGraphIso
    (fused (graph core1223) (root 9) 0 2) DegreeTwoThreeSpectrum1918.graph fusedMap1223=true := by decide +kernel
theorem certified1223 : Certified (graph core1223) (root 9) 0 2 :=
  of_native_maps core1223 DegreeTwoThreeSpectrum1867.graph DegreeTwoThreeSpectrum1918.graph
    sourceMap1223 fusedMap1223 sourceMap1223_checked fusedMap1223_checked
    DegreeTwoThreeFiniteComparisons.comparison1223
#print axioms sourceMap1223_checked
#print axioms fusedMap1223_checked
#print axioms certified1223
def sourceMap1223swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,8,5,6,2,3,4,7] (sourceLabel 9 2 0 v)
def fusedMap1223swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,6,7,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1223swap_checked : acceptsGraphIso
    (source (graph core1223) (root 9) 2 0) DegreeTwoThreeSpectrum1867.graph sourceMap1223swap=true := by decide +kernel
theorem fusedMap1223swap_checked : acceptsGraphIso
    (fused (graph core1223) (root 9) 2 0) DegreeTwoThreeSpectrum1918.graph fusedMap1223swap=true := by decide +kernel
theorem certified1223swap : Certified (graph core1223) (root 9) 2 0 :=
  of_native_maps core1223 DegreeTwoThreeSpectrum1867.graph DegreeTwoThreeSpectrum1918.graph
    sourceMap1223swap fusedMap1223swap sourceMap1223swap_checked fusedMap1223swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1223
#print axioms sourceMap1223swap_checked
#print axioms fusedMap1223swap_checked
#print axioms certified1223swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
