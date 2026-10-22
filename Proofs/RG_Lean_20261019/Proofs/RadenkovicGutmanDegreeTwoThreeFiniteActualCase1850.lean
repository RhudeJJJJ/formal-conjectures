/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1850 : Family 10 := level10.get ⟨1255,by decide⟩
def sourceMap1850 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1850 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1850_checked : acceptsGraphIso
    (source (graph core1850) (root 10) 0 2) DegreeTwoThreeSpectrum3398.graph sourceMap1850=true := by decide +kernel
theorem fusedMap1850_checked : acceptsGraphIso
    (fused (graph core1850) (root 10) 0 2) DegreeTwoThreeSpectrum3400.graph fusedMap1850=true := by decide +kernel
theorem certified1850 : Certified (graph core1850) (root 10) 0 2 :=
  of_native_maps core1850 DegreeTwoThreeSpectrum3398.graph DegreeTwoThreeSpectrum3400.graph
    sourceMap1850 fusedMap1850 sourceMap1850_checked fusedMap1850_checked
    DegreeTwoThreeFiniteComparisons.comparison1850
#print axioms sourceMap1850_checked
#print axioms fusedMap1850_checked
#print axioms certified1850
def sourceMap1850swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1850swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1850swap_checked : acceptsGraphIso
    (source (graph core1850) (root 10) 2 0) DegreeTwoThreeSpectrum3398.graph sourceMap1850swap=true := by decide +kernel
theorem fusedMap1850swap_checked : acceptsGraphIso
    (fused (graph core1850) (root 10) 2 0) DegreeTwoThreeSpectrum3400.graph fusedMap1850swap=true := by decide +kernel
theorem certified1850swap : Certified (graph core1850) (root 10) 2 0 :=
  of_native_maps core1850 DegreeTwoThreeSpectrum3398.graph DegreeTwoThreeSpectrum3400.graph
    sourceMap1850swap fusedMap1850swap sourceMap1850swap_checked fusedMap1850swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1850
#print axioms sourceMap1850swap_checked
#print axioms fusedMap1850swap_checked
#print axioms certified1850swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
