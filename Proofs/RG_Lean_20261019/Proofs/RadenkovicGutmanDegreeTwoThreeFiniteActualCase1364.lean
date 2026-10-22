/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1364 : Family 9 := level9.get ⟨511,by decide⟩
def sourceMap1364 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,4,5,6,1,2,3] (sourceLabel 9 0 2 v)
def fusedMap1364 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1364_checked : acceptsGraphIso
    (source (graph core1364) (root 9) 0 2) DegreeTwoThreeSpectrum2210.graph sourceMap1364=true := by decide +kernel
theorem fusedMap1364_checked : acceptsGraphIso
    (fused (graph core1364) (root 9) 0 2) DegreeTwoThreeSpectrum2221.graph fusedMap1364=true := by decide +kernel
theorem certified1364 : Certified (graph core1364) (root 9) 0 2 :=
  of_native_maps core1364 DegreeTwoThreeSpectrum2210.graph DegreeTwoThreeSpectrum2221.graph
    sourceMap1364 fusedMap1364 sourceMap1364_checked fusedMap1364_checked
    DegreeTwoThreeFiniteComparisons.comparison1364
#print axioms sourceMap1364_checked
#print axioms fusedMap1364_checked
#print axioms certified1364
def sourceMap1364swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,4,5,1,2,3,6] (sourceLabel 9 2 0 v)
def fusedMap1364swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1364swap_checked : acceptsGraphIso
    (source (graph core1364) (root 9) 2 0) DegreeTwoThreeSpectrum2210.graph sourceMap1364swap=true := by decide +kernel
theorem fusedMap1364swap_checked : acceptsGraphIso
    (fused (graph core1364) (root 9) 2 0) DegreeTwoThreeSpectrum2221.graph fusedMap1364swap=true := by decide +kernel
theorem certified1364swap : Certified (graph core1364) (root 9) 2 0 :=
  of_native_maps core1364 DegreeTwoThreeSpectrum2210.graph DegreeTwoThreeSpectrum2221.graph
    sourceMap1364swap fusedMap1364swap sourceMap1364swap_checked fusedMap1364swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1364
#print axioms sourceMap1364swap_checked
#print axioms fusedMap1364swap_checked
#print axioms certified1364swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
