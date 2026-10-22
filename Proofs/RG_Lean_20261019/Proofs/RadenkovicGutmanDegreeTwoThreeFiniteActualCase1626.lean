/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1626 : Family 10 := level10.get ⟨674,by decide⟩
def sourceMap1626 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1626 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1626_checked : acceptsGraphIso
    (source (graph core1626) (root 10) 0 2) DegreeTwoThreeSpectrum2638.graph sourceMap1626=true := by decide +kernel
theorem fusedMap1626_checked : acceptsGraphIso
    (fused (graph core1626) (root 10) 0 2) DegreeTwoThreeSpectrum2635.graph fusedMap1626=true := by decide +kernel
theorem certified1626 : Certified (graph core1626) (root 10) 0 2 :=
  of_native_maps core1626 DegreeTwoThreeSpectrum2638.graph DegreeTwoThreeSpectrum2635.graph
    sourceMap1626 fusedMap1626 sourceMap1626_checked fusedMap1626_checked
    DegreeTwoThreeFiniteComparisons.comparison1626
#print axioms sourceMap1626_checked
#print axioms fusedMap1626_checked
#print axioms certified1626
def sourceMap1626swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1626swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1626swap_checked : acceptsGraphIso
    (source (graph core1626) (root 10) 2 0) DegreeTwoThreeSpectrum2638.graph sourceMap1626swap=true := by decide +kernel
theorem fusedMap1626swap_checked : acceptsGraphIso
    (fused (graph core1626) (root 10) 2 0) DegreeTwoThreeSpectrum2635.graph fusedMap1626swap=true := by decide +kernel
theorem certified1626swap : Certified (graph core1626) (root 10) 2 0 :=
  of_native_maps core1626 DegreeTwoThreeSpectrum2638.graph DegreeTwoThreeSpectrum2635.graph
    sourceMap1626swap fusedMap1626swap sourceMap1626swap_checked fusedMap1626swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1626
#print axioms sourceMap1626swap_checked
#print axioms fusedMap1626swap_checked
#print axioms certified1626swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
