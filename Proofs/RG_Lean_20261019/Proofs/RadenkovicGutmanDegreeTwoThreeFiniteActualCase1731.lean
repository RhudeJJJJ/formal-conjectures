/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1731 : Family 10 := level10.get ⟨959,by decide⟩
def sourceMap1731 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1731 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1731_checked : acceptsGraphIso
    (source (graph core1731) (root 10) 0 2) DegreeTwoThreeSpectrum3715.graph sourceMap1731=true := by decide +kernel
theorem fusedMap1731_checked : acceptsGraphIso
    (fused (graph core1731) (root 10) 0 2) DegreeTwoThreeSpectrum2983.graph fusedMap1731=true := by decide +kernel
theorem certified1731 : Certified (graph core1731) (root 10) 0 2 :=
  of_native_maps core1731 DegreeTwoThreeSpectrum3715.graph DegreeTwoThreeSpectrum2983.graph
    sourceMap1731 fusedMap1731 sourceMap1731_checked fusedMap1731_checked
    DegreeTwoThreeFiniteComparisons.comparison1731
#print axioms sourceMap1731_checked
#print axioms fusedMap1731_checked
#print axioms certified1731
def sourceMap1731swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1731swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1731swap_checked : acceptsGraphIso
    (source (graph core1731) (root 10) 2 0) DegreeTwoThreeSpectrum3715.graph sourceMap1731swap=true := by decide +kernel
theorem fusedMap1731swap_checked : acceptsGraphIso
    (fused (graph core1731) (root 10) 2 0) DegreeTwoThreeSpectrum2983.graph fusedMap1731swap=true := by decide +kernel
theorem certified1731swap : Certified (graph core1731) (root 10) 2 0 :=
  of_native_maps core1731 DegreeTwoThreeSpectrum3715.graph DegreeTwoThreeSpectrum2983.graph
    sourceMap1731swap fusedMap1731swap sourceMap1731swap_checked fusedMap1731swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1731
#print axioms sourceMap1731swap_checked
#print axioms fusedMap1731swap_checked
#print axioms certified1731swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
