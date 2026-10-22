/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1705 : Family 10 := level10.get ⟨892,by decide⟩
def sourceMap1705 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1705 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1705_checked : acceptsGraphIso
    (source (graph core1705) (root 10) 0 2) DegreeTwoThreeSpectrum3658.graph sourceMap1705=true := by decide +kernel
theorem fusedMap1705_checked : acceptsGraphIso
    (fused (graph core1705) (root 10) 0 2) DegreeTwoThreeSpectrum2902.graph fusedMap1705=true := by decide +kernel
theorem certified1705 : Certified (graph core1705) (root 10) 0 2 :=
  of_native_maps core1705 DegreeTwoThreeSpectrum3658.graph DegreeTwoThreeSpectrum2902.graph
    sourceMap1705 fusedMap1705 sourceMap1705_checked fusedMap1705_checked
    DegreeTwoThreeFiniteComparisons.comparison1705
#print axioms sourceMap1705_checked
#print axioms fusedMap1705_checked
#print axioms certified1705
def sourceMap1705swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1705swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1705swap_checked : acceptsGraphIso
    (source (graph core1705) (root 10) 2 0) DegreeTwoThreeSpectrum3658.graph sourceMap1705swap=true := by decide +kernel
theorem fusedMap1705swap_checked : acceptsGraphIso
    (fused (graph core1705) (root 10) 2 0) DegreeTwoThreeSpectrum2902.graph fusedMap1705swap=true := by decide +kernel
theorem certified1705swap : Certified (graph core1705) (root 10) 2 0 :=
  of_native_maps core1705 DegreeTwoThreeSpectrum3658.graph DegreeTwoThreeSpectrum2902.graph
    sourceMap1705swap fusedMap1705swap sourceMap1705swap_checked fusedMap1705swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1705
#print axioms sourceMap1705swap_checked
#print axioms fusedMap1705swap_checked
#print axioms certified1705swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
