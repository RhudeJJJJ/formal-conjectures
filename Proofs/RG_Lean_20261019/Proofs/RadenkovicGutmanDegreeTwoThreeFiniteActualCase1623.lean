/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1623 : Family 10 := level10.get ⟨668,by decide⟩
def sourceMap1623 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,12,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1623 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1623_checked : acceptsGraphIso
    (source (graph core1623) (root 10) 0 2) DegreeTwoThreeSpectrum3364.graph sourceMap1623=true := by decide +kernel
theorem fusedMap1623_checked : acceptsGraphIso
    (fused (graph core1623) (root 10) 0 2) DegreeTwoThreeSpectrum2617.graph fusedMap1623=true := by decide +kernel
theorem certified1623 : Certified (graph core1623) (root 10) 0 2 :=
  of_native_maps core1623 DegreeTwoThreeSpectrum3364.graph DegreeTwoThreeSpectrum2617.graph
    sourceMap1623 fusedMap1623 sourceMap1623_checked fusedMap1623_checked
    DegreeTwoThreeFiniteComparisons.comparison1623
#print axioms sourceMap1623_checked
#print axioms fusedMap1623_checked
#print axioms certified1623
def sourceMap1623swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,7,8,9,12] (sourceLabel 10 2 0 v)
def fusedMap1623swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1623swap_checked : acceptsGraphIso
    (source (graph core1623) (root 10) 2 0) DegreeTwoThreeSpectrum3364.graph sourceMap1623swap=true := by decide +kernel
theorem fusedMap1623swap_checked : acceptsGraphIso
    (fused (graph core1623) (root 10) 2 0) DegreeTwoThreeSpectrum2617.graph fusedMap1623swap=true := by decide +kernel
theorem certified1623swap : Certified (graph core1623) (root 10) 2 0 :=
  of_native_maps core1623 DegreeTwoThreeSpectrum3364.graph DegreeTwoThreeSpectrum2617.graph
    sourceMap1623swap fusedMap1623swap sourceMap1623swap_checked fusedMap1623swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1623
#print axioms sourceMap1623swap_checked
#print axioms fusedMap1623swap_checked
#print axioms certified1623swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
