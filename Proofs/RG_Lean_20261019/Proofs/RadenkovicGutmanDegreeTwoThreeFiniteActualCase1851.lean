/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1851 : Family 10 := level10.get ⟨1260,by decide⟩
def sourceMap1851 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1851 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1851_checked : acceptsGraphIso
    (source (graph core1851) (root 10) 0 2) DegreeTwoThreeSpectrum3405.graph sourceMap1851=true := by decide +kernel
theorem fusedMap1851_checked : acceptsGraphIso
    (fused (graph core1851) (root 10) 0 2) DegreeTwoThreeSpectrum3406.graph fusedMap1851=true := by decide +kernel
theorem certified1851 : Certified (graph core1851) (root 10) 0 2 :=
  of_native_maps core1851 DegreeTwoThreeSpectrum3405.graph DegreeTwoThreeSpectrum3406.graph
    sourceMap1851 fusedMap1851 sourceMap1851_checked fusedMap1851_checked
    DegreeTwoThreeFiniteComparisons.comparison1851
#print axioms sourceMap1851_checked
#print axioms fusedMap1851_checked
#print axioms certified1851
def sourceMap1851swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1851swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1851swap_checked : acceptsGraphIso
    (source (graph core1851) (root 10) 2 0) DegreeTwoThreeSpectrum3405.graph sourceMap1851swap=true := by decide +kernel
theorem fusedMap1851swap_checked : acceptsGraphIso
    (fused (graph core1851) (root 10) 2 0) DegreeTwoThreeSpectrum3406.graph fusedMap1851swap=true := by decide +kernel
theorem certified1851swap : Certified (graph core1851) (root 10) 2 0 :=
  of_native_maps core1851 DegreeTwoThreeSpectrum3405.graph DegreeTwoThreeSpectrum3406.graph
    sourceMap1851swap fusedMap1851swap sourceMap1851swap_checked fusedMap1851swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1851
#print axioms sourceMap1851swap_checked
#print axioms fusedMap1851swap_checked
#print axioms certified1851swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
