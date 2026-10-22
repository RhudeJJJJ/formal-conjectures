/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1732 : Family 10 := level10.get ⟨960,by decide⟩
def sourceMap1732 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1732 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,5,6,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1732_checked : acceptsGraphIso
    (source (graph core1732) (root 10) 0 2) DegreeTwoThreeSpectrum3686.graph sourceMap1732=true := by decide +kernel
theorem fusedMap1732_checked : acceptsGraphIso
    (fused (graph core1732) (root 10) 0 2) DegreeTwoThreeSpectrum2978.graph fusedMap1732=true := by decide +kernel
theorem certified1732 : Certified (graph core1732) (root 10) 0 2 :=
  of_native_maps core1732 DegreeTwoThreeSpectrum3686.graph DegreeTwoThreeSpectrum2978.graph
    sourceMap1732 fusedMap1732 sourceMap1732_checked fusedMap1732_checked
    DegreeTwoThreeFiniteComparisons.comparison1732
#print axioms sourceMap1732_checked
#print axioms fusedMap1732_checked
#print axioms certified1732
def sourceMap1732swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1732swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,5,6,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1732swap_checked : acceptsGraphIso
    (source (graph core1732) (root 10) 2 0) DegreeTwoThreeSpectrum3686.graph sourceMap1732swap=true := by decide +kernel
theorem fusedMap1732swap_checked : acceptsGraphIso
    (fused (graph core1732) (root 10) 2 0) DegreeTwoThreeSpectrum2978.graph fusedMap1732swap=true := by decide +kernel
theorem certified1732swap : Certified (graph core1732) (root 10) 2 0 :=
  of_native_maps core1732 DegreeTwoThreeSpectrum3686.graph DegreeTwoThreeSpectrum2978.graph
    sourceMap1732swap fusedMap1732swap sourceMap1732swap_checked fusedMap1732swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1732
#print axioms sourceMap1732swap_checked
#print axioms fusedMap1732swap_checked
#print axioms certified1732swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
