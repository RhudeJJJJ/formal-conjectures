/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1833 : Family 10 := level10.get ⟨1212,by decide⟩
def sourceMap1833 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1833 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1833_checked : acceptsGraphIso
    (source (graph core1833) (root 10) 0 2) DegreeTwoThreeSpectrum3347.graph sourceMap1833=true := by decide +kernel
theorem fusedMap1833_checked : acceptsGraphIso
    (fused (graph core1833) (root 10) 0 2) DegreeTwoThreeSpectrum3344.graph fusedMap1833=true := by decide +kernel
theorem certified1833 : Certified (graph core1833) (root 10) 0 2 :=
  of_native_maps core1833 DegreeTwoThreeSpectrum3347.graph DegreeTwoThreeSpectrum3344.graph
    sourceMap1833 fusedMap1833 sourceMap1833_checked fusedMap1833_checked
    DegreeTwoThreeFiniteComparisons.comparison1833
#print axioms sourceMap1833_checked
#print axioms fusedMap1833_checked
#print axioms certified1833
def sourceMap1833swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1833swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1833swap_checked : acceptsGraphIso
    (source (graph core1833) (root 10) 2 0) DegreeTwoThreeSpectrum3347.graph sourceMap1833swap=true := by decide +kernel
theorem fusedMap1833swap_checked : acceptsGraphIso
    (fused (graph core1833) (root 10) 2 0) DegreeTwoThreeSpectrum3344.graph fusedMap1833swap=true := by decide +kernel
theorem certified1833swap : Certified (graph core1833) (root 10) 2 0 :=
  of_native_maps core1833 DegreeTwoThreeSpectrum3347.graph DegreeTwoThreeSpectrum3344.graph
    sourceMap1833swap fusedMap1833swap sourceMap1833swap_checked fusedMap1833swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1833
#print axioms sourceMap1833swap_checked
#print axioms fusedMap1833swap_checked
#print axioms certified1833swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
