/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1810 : Family 10 := level10.get ⟨1160,by decide⟩
def sourceMap1810 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1810 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1810_checked : acceptsGraphIso
    (source (graph core1810) (root 10) 0 2) DegreeTwoThreeSpectrum3256.graph sourceMap1810=true := by decide +kernel
theorem fusedMap1810_checked : acceptsGraphIso
    (fused (graph core1810) (root 10) 0 2) DegreeTwoThreeSpectrum3258.graph fusedMap1810=true := by decide +kernel
theorem certified1810 : Certified (graph core1810) (root 10) 0 2 :=
  of_native_maps core1810 DegreeTwoThreeSpectrum3256.graph DegreeTwoThreeSpectrum3258.graph
    sourceMap1810 fusedMap1810 sourceMap1810_checked fusedMap1810_checked
    DegreeTwoThreeFiniteComparisons.comparison1810
#print axioms sourceMap1810_checked
#print axioms fusedMap1810_checked
#print axioms certified1810
def sourceMap1810swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1810swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1810swap_checked : acceptsGraphIso
    (source (graph core1810) (root 10) 2 0) DegreeTwoThreeSpectrum3256.graph sourceMap1810swap=true := by decide +kernel
theorem fusedMap1810swap_checked : acceptsGraphIso
    (fused (graph core1810) (root 10) 2 0) DegreeTwoThreeSpectrum3258.graph fusedMap1810swap=true := by decide +kernel
theorem certified1810swap : Certified (graph core1810) (root 10) 2 0 :=
  of_native_maps core1810 DegreeTwoThreeSpectrum3256.graph DegreeTwoThreeSpectrum3258.graph
    sourceMap1810swap fusedMap1810swap sourceMap1810swap_checked fusedMap1810swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1810
#print axioms sourceMap1810swap_checked
#print axioms fusedMap1810swap_checked
#print axioms certified1810swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
