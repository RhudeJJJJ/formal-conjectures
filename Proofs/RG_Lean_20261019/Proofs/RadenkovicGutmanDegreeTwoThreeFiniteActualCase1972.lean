/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1972 : Family 10 := level10.get ⟨1555,by decide⟩
def sourceMap1972 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1972 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1972_checked : acceptsGraphIso
    (source (graph core1972) (root 10) 0 2) DegreeTwoThreeSpectrum3755.graph sourceMap1972=true := by decide +kernel
theorem fusedMap1972_checked : acceptsGraphIso
    (fused (graph core1972) (root 10) 0 2) DegreeTwoThreeSpectrum3034.graph fusedMap1972=true := by decide +kernel
theorem certified1972 : Certified (graph core1972) (root 10) 0 2 :=
  of_native_maps core1972 DegreeTwoThreeSpectrum3755.graph DegreeTwoThreeSpectrum3034.graph
    sourceMap1972 fusedMap1972 sourceMap1972_checked fusedMap1972_checked
    DegreeTwoThreeFiniteComparisons.comparison1972
#print axioms sourceMap1972_checked
#print axioms fusedMap1972_checked
#print axioms certified1972
def sourceMap1972swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1972swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1972swap_checked : acceptsGraphIso
    (source (graph core1972) (root 10) 2 0) DegreeTwoThreeSpectrum3755.graph sourceMap1972swap=true := by decide +kernel
theorem fusedMap1972swap_checked : acceptsGraphIso
    (fused (graph core1972) (root 10) 2 0) DegreeTwoThreeSpectrum3034.graph fusedMap1972swap=true := by decide +kernel
theorem certified1972swap : Certified (graph core1972) (root 10) 2 0 :=
  of_native_maps core1972 DegreeTwoThreeSpectrum3755.graph DegreeTwoThreeSpectrum3034.graph
    sourceMap1972swap fusedMap1972swap sourceMap1972swap_checked fusedMap1972swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1972
#print axioms sourceMap1972swap_checked
#print axioms fusedMap1972swap_checked
#print axioms certified1972swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
