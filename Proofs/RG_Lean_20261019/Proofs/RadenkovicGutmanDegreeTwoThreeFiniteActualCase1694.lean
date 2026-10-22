/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1694 : Family 10 := level10.get ⟨868,by decide⟩
def sourceMap1694 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1694 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1694_checked : acceptsGraphIso
    (source (graph core1694) (root 10) 0 2) DegreeTwoThreeSpectrum3688.graph sourceMap1694=true := by decide +kernel
theorem fusedMap1694_checked : acceptsGraphIso
    (fused (graph core1694) (root 10) 0 2) DegreeTwoThreeSpectrum2860.graph fusedMap1694=true := by decide +kernel
theorem certified1694 : Certified (graph core1694) (root 10) 0 2 :=
  of_native_maps core1694 DegreeTwoThreeSpectrum3688.graph DegreeTwoThreeSpectrum2860.graph
    sourceMap1694 fusedMap1694 sourceMap1694_checked fusedMap1694_checked
    DegreeTwoThreeFiniteComparisons.comparison1694
#print axioms sourceMap1694_checked
#print axioms fusedMap1694_checked
#print axioms certified1694
def sourceMap1694swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1694swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1694swap_checked : acceptsGraphIso
    (source (graph core1694) (root 10) 2 0) DegreeTwoThreeSpectrum3688.graph sourceMap1694swap=true := by decide +kernel
theorem fusedMap1694swap_checked : acceptsGraphIso
    (fused (graph core1694) (root 10) 2 0) DegreeTwoThreeSpectrum2860.graph fusedMap1694swap=true := by decide +kernel
theorem certified1694swap : Certified (graph core1694) (root 10) 2 0 :=
  of_native_maps core1694 DegreeTwoThreeSpectrum3688.graph DegreeTwoThreeSpectrum2860.graph
    sourceMap1694swap fusedMap1694swap sourceMap1694swap_checked fusedMap1694swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1694
#print axioms sourceMap1694swap_checked
#print axioms fusedMap1694swap_checked
#print axioms certified1694swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
