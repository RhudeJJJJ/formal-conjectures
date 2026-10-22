/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1698 : Family 10 := level10.get ⟨877,by decide⟩
def sourceMap1698 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1698 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1698_checked : acceptsGraphIso
    (source (graph core1698) (root 10) 0 2) DegreeTwoThreeSpectrum3696.graph sourceMap1698=true := by decide +kernel
theorem fusedMap1698_checked : acceptsGraphIso
    (fused (graph core1698) (root 10) 0 2) DegreeTwoThreeSpectrum2872.graph fusedMap1698=true := by decide +kernel
theorem certified1698 : Certified (graph core1698) (root 10) 0 2 :=
  of_native_maps core1698 DegreeTwoThreeSpectrum3696.graph DegreeTwoThreeSpectrum2872.graph
    sourceMap1698 fusedMap1698 sourceMap1698_checked fusedMap1698_checked
    DegreeTwoThreeFiniteComparisons.comparison1698
#print axioms sourceMap1698_checked
#print axioms fusedMap1698_checked
#print axioms certified1698
def sourceMap1698swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1698swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1698swap_checked : acceptsGraphIso
    (source (graph core1698) (root 10) 2 0) DegreeTwoThreeSpectrum3696.graph sourceMap1698swap=true := by decide +kernel
theorem fusedMap1698swap_checked : acceptsGraphIso
    (fused (graph core1698) (root 10) 2 0) DegreeTwoThreeSpectrum2872.graph fusedMap1698swap=true := by decide +kernel
theorem certified1698swap : Certified (graph core1698) (root 10) 2 0 :=
  of_native_maps core1698 DegreeTwoThreeSpectrum3696.graph DegreeTwoThreeSpectrum2872.graph
    sourceMap1698swap fusedMap1698swap sourceMap1698swap_checked fusedMap1698swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1698
#print axioms sourceMap1698swap_checked
#print axioms fusedMap1698swap_checked
#print axioms certified1698swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
