/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1661 : Family 10 := level10.get ⟨778,by decide⟩
def sourceMap1661 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1661 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1661_checked : acceptsGraphIso
    (source (graph core1661) (root 10) 0 2) DegreeTwoThreeSpectrum3561.graph sourceMap1661=true := by decide +kernel
theorem fusedMap1661_checked : acceptsGraphIso
    (fused (graph core1661) (root 10) 0 2) DegreeTwoThreeSpectrum2746.graph fusedMap1661=true := by decide +kernel
theorem certified1661 : Certified (graph core1661) (root 10) 0 2 :=
  of_native_maps core1661 DegreeTwoThreeSpectrum3561.graph DegreeTwoThreeSpectrum2746.graph
    sourceMap1661 fusedMap1661 sourceMap1661_checked fusedMap1661_checked
    DegreeTwoThreeFiniteComparisons.comparison1661
#print axioms sourceMap1661_checked
#print axioms fusedMap1661_checked
#print axioms certified1661
def sourceMap1661swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1661swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1661swap_checked : acceptsGraphIso
    (source (graph core1661) (root 10) 2 0) DegreeTwoThreeSpectrum3561.graph sourceMap1661swap=true := by decide +kernel
theorem fusedMap1661swap_checked : acceptsGraphIso
    (fused (graph core1661) (root 10) 2 0) DegreeTwoThreeSpectrum2746.graph fusedMap1661swap=true := by decide +kernel
theorem certified1661swap : Certified (graph core1661) (root 10) 2 0 :=
  of_native_maps core1661 DegreeTwoThreeSpectrum3561.graph DegreeTwoThreeSpectrum2746.graph
    sourceMap1661swap fusedMap1661swap sourceMap1661swap_checked fusedMap1661swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1661
#print axioms sourceMap1661swap_checked
#print axioms fusedMap1661swap_checked
#print axioms certified1661swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
