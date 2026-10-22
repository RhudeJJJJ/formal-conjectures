/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1762 : Family 10 := level10.get ⟨1039,by decide⟩
def sourceMap1762 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1762 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1762_checked : acceptsGraphIso
    (source (graph core1762) (root 10) 0 2) DegreeTwoThreeSpectrum3072.graph sourceMap1762=true := by decide +kernel
theorem fusedMap1762_checked : acceptsGraphIso
    (fused (graph core1762) (root 10) 0 2) DegreeTwoThreeSpectrum3073.graph fusedMap1762=true := by decide +kernel
theorem certified1762 : Certified (graph core1762) (root 10) 0 2 :=
  of_native_maps core1762 DegreeTwoThreeSpectrum3072.graph DegreeTwoThreeSpectrum3073.graph
    sourceMap1762 fusedMap1762 sourceMap1762_checked fusedMap1762_checked
    DegreeTwoThreeFiniteComparisons.comparison1762
#print axioms sourceMap1762_checked
#print axioms fusedMap1762_checked
#print axioms certified1762
def sourceMap1762swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1762swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1762swap_checked : acceptsGraphIso
    (source (graph core1762) (root 10) 2 0) DegreeTwoThreeSpectrum3072.graph sourceMap1762swap=true := by decide +kernel
theorem fusedMap1762swap_checked : acceptsGraphIso
    (fused (graph core1762) (root 10) 2 0) DegreeTwoThreeSpectrum3073.graph fusedMap1762swap=true := by decide +kernel
theorem certified1762swap : Certified (graph core1762) (root 10) 2 0 :=
  of_native_maps core1762 DegreeTwoThreeSpectrum3072.graph DegreeTwoThreeSpectrum3073.graph
    sourceMap1762swap fusedMap1762swap sourceMap1762swap_checked fusedMap1762swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1762
#print axioms sourceMap1762swap_checked
#print axioms fusedMap1762swap_checked
#print axioms certified1762swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
