/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1856 : Family 10 := level10.get ⟨1271,by decide⟩
def sourceMap1856 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1856 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1856_checked : acceptsGraphIso
    (source (graph core1856) (root 10) 0 2) DegreeTwoThreeSpectrum3423.graph sourceMap1856=true := by decide +kernel
theorem fusedMap1856_checked : acceptsGraphIso
    (fused (graph core1856) (root 10) 0 2) DegreeTwoThreeSpectrum3424.graph fusedMap1856=true := by decide +kernel
theorem certified1856 : Certified (graph core1856) (root 10) 0 2 :=
  of_native_maps core1856 DegreeTwoThreeSpectrum3423.graph DegreeTwoThreeSpectrum3424.graph
    sourceMap1856 fusedMap1856 sourceMap1856_checked fusedMap1856_checked
    DegreeTwoThreeFiniteComparisons.comparison1856
#print axioms sourceMap1856_checked
#print axioms fusedMap1856_checked
#print axioms certified1856
def sourceMap1856swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1856swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1856swap_checked : acceptsGraphIso
    (source (graph core1856) (root 10) 2 0) DegreeTwoThreeSpectrum3423.graph sourceMap1856swap=true := by decide +kernel
theorem fusedMap1856swap_checked : acceptsGraphIso
    (fused (graph core1856) (root 10) 2 0) DegreeTwoThreeSpectrum3424.graph fusedMap1856swap=true := by decide +kernel
theorem certified1856swap : Certified (graph core1856) (root 10) 2 0 :=
  of_native_maps core1856 DegreeTwoThreeSpectrum3423.graph DegreeTwoThreeSpectrum3424.graph
    sourceMap1856swap fusedMap1856swap sourceMap1856swap_checked fusedMap1856swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1856
#print axioms sourceMap1856swap_checked
#print axioms fusedMap1856swap_checked
#print axioms certified1856swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
