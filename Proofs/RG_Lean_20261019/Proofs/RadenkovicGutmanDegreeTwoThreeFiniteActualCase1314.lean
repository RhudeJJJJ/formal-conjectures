/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1314 : Family 9 := level9.get ⟨395,by decide⟩
def sourceMap1314 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1314 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1314_checked : acceptsGraphIso
    (source (graph core1314) (root 9) 0 2) DegreeTwoThreeSpectrum2050.graph sourceMap1314=true := by decide +kernel
theorem fusedMap1314_checked : acceptsGraphIso
    (fused (graph core1314) (root 9) 0 2) DegreeTwoThreeSpectrum2051.graph fusedMap1314=true := by decide +kernel
theorem certified1314 : Certified (graph core1314) (root 9) 0 2 :=
  of_native_maps core1314 DegreeTwoThreeSpectrum2050.graph DegreeTwoThreeSpectrum2051.graph
    sourceMap1314 fusedMap1314 sourceMap1314_checked fusedMap1314_checked
    DegreeTwoThreeFiniteComparisons.comparison1314
#print axioms sourceMap1314_checked
#print axioms fusedMap1314_checked
#print axioms certified1314
def sourceMap1314swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1314swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1314swap_checked : acceptsGraphIso
    (source (graph core1314) (root 9) 2 0) DegreeTwoThreeSpectrum2050.graph sourceMap1314swap=true := by decide +kernel
theorem fusedMap1314swap_checked : acceptsGraphIso
    (fused (graph core1314) (root 9) 2 0) DegreeTwoThreeSpectrum2051.graph fusedMap1314swap=true := by decide +kernel
theorem certified1314swap : Certified (graph core1314) (root 9) 2 0 :=
  of_native_maps core1314 DegreeTwoThreeSpectrum2050.graph DegreeTwoThreeSpectrum2051.graph
    sourceMap1314swap fusedMap1314swap sourceMap1314swap_checked fusedMap1314swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1314
#print axioms sourceMap1314swap_checked
#print axioms fusedMap1314swap_checked
#print axioms certified1314swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
