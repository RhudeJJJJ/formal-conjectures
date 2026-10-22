/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1725 : Family 10 := level10.get ⟨946,by decide⟩
def sourceMap1725 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1725 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1725_checked : acceptsGraphIso
    (source (graph core1725) (root 10) 0 2) DegreeTwoThreeSpectrum3684.graph sourceMap1725=true := by decide +kernel
theorem fusedMap1725_checked : acceptsGraphIso
    (fused (graph core1725) (root 10) 0 2) DegreeTwoThreeSpectrum2968.graph fusedMap1725=true := by decide +kernel
theorem certified1725 : Certified (graph core1725) (root 10) 0 2 :=
  of_native_maps core1725 DegreeTwoThreeSpectrum3684.graph DegreeTwoThreeSpectrum2968.graph
    sourceMap1725 fusedMap1725 sourceMap1725_checked fusedMap1725_checked
    DegreeTwoThreeFiniteComparisons.comparison1725
#print axioms sourceMap1725_checked
#print axioms fusedMap1725_checked
#print axioms certified1725
def sourceMap1725swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1725swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1725swap_checked : acceptsGraphIso
    (source (graph core1725) (root 10) 2 0) DegreeTwoThreeSpectrum3684.graph sourceMap1725swap=true := by decide +kernel
theorem fusedMap1725swap_checked : acceptsGraphIso
    (fused (graph core1725) (root 10) 2 0) DegreeTwoThreeSpectrum2968.graph fusedMap1725swap=true := by decide +kernel
theorem certified1725swap : Certified (graph core1725) (root 10) 2 0 :=
  of_native_maps core1725 DegreeTwoThreeSpectrum3684.graph DegreeTwoThreeSpectrum2968.graph
    sourceMap1725swap fusedMap1725swap sourceMap1725swap_checked fusedMap1725swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1725
#print axioms sourceMap1725swap_checked
#print axioms fusedMap1725swap_checked
#print axioms certified1725swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
