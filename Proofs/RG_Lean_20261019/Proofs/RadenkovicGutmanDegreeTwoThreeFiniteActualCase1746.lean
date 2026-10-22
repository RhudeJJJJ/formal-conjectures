/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1746 : Family 10 := level10.get ⟨984,by decide⟩
def sourceMap1746 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1746 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1746_checked : acceptsGraphIso
    (source (graph core1746) (root 10) 0 2) DegreeTwoThreeSpectrum3491.graph sourceMap1746=true := by decide +kernel
theorem fusedMap1746_checked : acceptsGraphIso
    (fused (graph core1746) (root 10) 0 2) DegreeTwoThreeSpectrum2950.graph fusedMap1746=true := by decide +kernel
theorem certified1746 : Certified (graph core1746) (root 10) 0 2 :=
  of_native_maps core1746 DegreeTwoThreeSpectrum3491.graph DegreeTwoThreeSpectrum2950.graph
    sourceMap1746 fusedMap1746 sourceMap1746_checked fusedMap1746_checked
    DegreeTwoThreeFiniteComparisons.comparison1746
#print axioms sourceMap1746_checked
#print axioms fusedMap1746_checked
#print axioms certified1746
def sourceMap1746swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1746swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1746swap_checked : acceptsGraphIso
    (source (graph core1746) (root 10) 2 0) DegreeTwoThreeSpectrum3491.graph sourceMap1746swap=true := by decide +kernel
theorem fusedMap1746swap_checked : acceptsGraphIso
    (fused (graph core1746) (root 10) 2 0) DegreeTwoThreeSpectrum2950.graph fusedMap1746swap=true := by decide +kernel
theorem certified1746swap : Certified (graph core1746) (root 10) 2 0 :=
  of_native_maps core1746 DegreeTwoThreeSpectrum3491.graph DegreeTwoThreeSpectrum2950.graph
    sourceMap1746swap fusedMap1746swap sourceMap1746swap_checked fusedMap1746swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1746
#print axioms sourceMap1746swap_checked
#print axioms fusedMap1746swap_checked
#print axioms certified1746swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
