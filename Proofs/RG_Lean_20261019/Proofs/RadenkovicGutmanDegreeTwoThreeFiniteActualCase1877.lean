/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1877 : Family 10 := level10.get ⟨1322,by decide⟩
def sourceMap1877 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1877 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1877_checked : acceptsGraphIso
    (source (graph core1877) (root 10) 0 2) DegreeTwoThreeSpectrum3496.graph sourceMap1877=true := by decide +kernel
theorem fusedMap1877_checked : acceptsGraphIso
    (fused (graph core1877) (root 10) 0 2) DegreeTwoThreeSpectrum3497.graph fusedMap1877=true := by decide +kernel
theorem certified1877 : Certified (graph core1877) (root 10) 0 2 :=
  of_native_maps core1877 DegreeTwoThreeSpectrum3496.graph DegreeTwoThreeSpectrum3497.graph
    sourceMap1877 fusedMap1877 sourceMap1877_checked fusedMap1877_checked
    DegreeTwoThreeFiniteComparisons.comparison1877
#print axioms sourceMap1877_checked
#print axioms fusedMap1877_checked
#print axioms certified1877
def sourceMap1877swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1877swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1877swap_checked : acceptsGraphIso
    (source (graph core1877) (root 10) 2 0) DegreeTwoThreeSpectrum3496.graph sourceMap1877swap=true := by decide +kernel
theorem fusedMap1877swap_checked : acceptsGraphIso
    (fused (graph core1877) (root 10) 2 0) DegreeTwoThreeSpectrum3497.graph fusedMap1877swap=true := by decide +kernel
theorem certified1877swap : Certified (graph core1877) (root 10) 2 0 :=
  of_native_maps core1877 DegreeTwoThreeSpectrum3496.graph DegreeTwoThreeSpectrum3497.graph
    sourceMap1877swap fusedMap1877swap sourceMap1877swap_checked fusedMap1877swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1877
#print axioms sourceMap1877swap_checked
#print axioms fusedMap1877swap_checked
#print axioms certified1877swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
