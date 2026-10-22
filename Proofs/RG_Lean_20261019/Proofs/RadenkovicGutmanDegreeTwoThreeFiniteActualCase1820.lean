/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1820 : Family 10 := level10.get ⟨1184,by decide⟩
def sourceMap1820 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1820 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1820_checked : acceptsGraphIso
    (source (graph core1820) (root 10) 0 2) DegreeTwoThreeSpectrum3299.graph sourceMap1820=true := by decide +kernel
theorem fusedMap1820_checked : acceptsGraphIso
    (fused (graph core1820) (root 10) 0 2) DegreeTwoThreeSpectrum3301.graph fusedMap1820=true := by decide +kernel
theorem certified1820 : Certified (graph core1820) (root 10) 0 2 :=
  of_native_maps core1820 DegreeTwoThreeSpectrum3299.graph DegreeTwoThreeSpectrum3301.graph
    sourceMap1820 fusedMap1820 sourceMap1820_checked fusedMap1820_checked
    DegreeTwoThreeFiniteComparisons.comparison1820
#print axioms sourceMap1820_checked
#print axioms fusedMap1820_checked
#print axioms certified1820
def sourceMap1820swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1820swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1820swap_checked : acceptsGraphIso
    (source (graph core1820) (root 10) 2 0) DegreeTwoThreeSpectrum3299.graph sourceMap1820swap=true := by decide +kernel
theorem fusedMap1820swap_checked : acceptsGraphIso
    (fused (graph core1820) (root 10) 2 0) DegreeTwoThreeSpectrum3301.graph fusedMap1820swap=true := by decide +kernel
theorem certified1820swap : Certified (graph core1820) (root 10) 2 0 :=
  of_native_maps core1820 DegreeTwoThreeSpectrum3299.graph DegreeTwoThreeSpectrum3301.graph
    sourceMap1820swap fusedMap1820swap sourceMap1820swap_checked fusedMap1820swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1820
#print axioms sourceMap1820swap_checked
#print axioms fusedMap1820swap_checked
#print axioms certified1820swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
