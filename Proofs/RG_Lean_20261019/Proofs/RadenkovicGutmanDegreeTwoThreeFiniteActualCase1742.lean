/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1742 : Family 10 := level10.get ⟨978,by decide⟩
def sourceMap1742 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1742 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1742_checked : acceptsGraphIso
    (source (graph core1742) (root 10) 0 2) DegreeTwoThreeSpectrum2911.graph sourceMap1742=true := by decide +kernel
theorem fusedMap1742_checked : acceptsGraphIso
    (fused (graph core1742) (root 10) 0 2) DegreeTwoThreeSpectrum2910.graph fusedMap1742=true := by decide +kernel
theorem certified1742 : Certified (graph core1742) (root 10) 0 2 :=
  of_native_maps core1742 DegreeTwoThreeSpectrum2911.graph DegreeTwoThreeSpectrum2910.graph
    sourceMap1742 fusedMap1742 sourceMap1742_checked fusedMap1742_checked
    DegreeTwoThreeFiniteComparisons.comparison1742
#print axioms sourceMap1742_checked
#print axioms fusedMap1742_checked
#print axioms certified1742
def sourceMap1742swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1742swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1742swap_checked : acceptsGraphIso
    (source (graph core1742) (root 10) 2 0) DegreeTwoThreeSpectrum2911.graph sourceMap1742swap=true := by decide +kernel
theorem fusedMap1742swap_checked : acceptsGraphIso
    (fused (graph core1742) (root 10) 2 0) DegreeTwoThreeSpectrum2910.graph fusedMap1742swap=true := by decide +kernel
theorem certified1742swap : Certified (graph core1742) (root 10) 2 0 :=
  of_native_maps core1742 DegreeTwoThreeSpectrum2911.graph DegreeTwoThreeSpectrum2910.graph
    sourceMap1742swap fusedMap1742swap sourceMap1742swap_checked fusedMap1742swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1742
#print axioms sourceMap1742swap_checked
#print axioms fusedMap1742swap_checked
#print axioms certified1742swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
