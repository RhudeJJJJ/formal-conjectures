/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1960 : Family 10 := level10.get ⟨1529,by decide⟩
def sourceMap1960 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1960 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1960_checked : acceptsGraphIso
    (source (graph core1960) (root 10) 0 2) DegreeTwoThreeSpectrum3739.graph sourceMap1960=true := by decide +kernel
theorem fusedMap1960_checked : acceptsGraphIso
    (fused (graph core1960) (root 10) 0 2) DegreeTwoThreeSpectrum3001.graph fusedMap1960=true := by decide +kernel
theorem certified1960 : Certified (graph core1960) (root 10) 0 2 :=
  of_native_maps core1960 DegreeTwoThreeSpectrum3739.graph DegreeTwoThreeSpectrum3001.graph
    sourceMap1960 fusedMap1960 sourceMap1960_checked fusedMap1960_checked
    DegreeTwoThreeFiniteComparisons.comparison1960
#print axioms sourceMap1960_checked
#print axioms fusedMap1960_checked
#print axioms certified1960
def sourceMap1960swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1960swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1960swap_checked : acceptsGraphIso
    (source (graph core1960) (root 10) 2 0) DegreeTwoThreeSpectrum3739.graph sourceMap1960swap=true := by decide +kernel
theorem fusedMap1960swap_checked : acceptsGraphIso
    (fused (graph core1960) (root 10) 2 0) DegreeTwoThreeSpectrum3001.graph fusedMap1960swap=true := by decide +kernel
theorem certified1960swap : Certified (graph core1960) (root 10) 2 0 :=
  of_native_maps core1960 DegreeTwoThreeSpectrum3739.graph DegreeTwoThreeSpectrum3001.graph
    sourceMap1960swap fusedMap1960swap sourceMap1960swap_checked fusedMap1960swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1960
#print axioms sourceMap1960swap_checked
#print axioms fusedMap1960swap_checked
#print axioms certified1960swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
