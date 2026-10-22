/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1690 : Family 10 := level10.get ⟨857,by decide⟩
def sourceMap1690 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1690 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1690_checked : acceptsGraphIso
    (source (graph core1690) (root 10) 0 2) DegreeTwoThreeSpectrum3674.graph sourceMap1690=true := by decide +kernel
theorem fusedMap1690_checked : acceptsGraphIso
    (fused (graph core1690) (root 10) 0 2) DegreeTwoThreeSpectrum2843.graph fusedMap1690=true := by decide +kernel
theorem certified1690 : Certified (graph core1690) (root 10) 0 2 :=
  of_native_maps core1690 DegreeTwoThreeSpectrum3674.graph DegreeTwoThreeSpectrum2843.graph
    sourceMap1690 fusedMap1690 sourceMap1690_checked fusedMap1690_checked
    DegreeTwoThreeFiniteComparisons.comparison1690
#print axioms sourceMap1690_checked
#print axioms fusedMap1690_checked
#print axioms certified1690
def sourceMap1690swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1690swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1690swap_checked : acceptsGraphIso
    (source (graph core1690) (root 10) 2 0) DegreeTwoThreeSpectrum3674.graph sourceMap1690swap=true := by decide +kernel
theorem fusedMap1690swap_checked : acceptsGraphIso
    (fused (graph core1690) (root 10) 2 0) DegreeTwoThreeSpectrum2843.graph fusedMap1690swap=true := by decide +kernel
theorem certified1690swap : Certified (graph core1690) (root 10) 2 0 :=
  of_native_maps core1690 DegreeTwoThreeSpectrum3674.graph DegreeTwoThreeSpectrum2843.graph
    sourceMap1690swap fusedMap1690swap sourceMap1690swap_checked fusedMap1690swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1690
#print axioms sourceMap1690swap_checked
#print axioms fusedMap1690swap_checked
#print axioms certified1690swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
