/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1898 : Family 10 := level10.get ⟨1367,by decide⟩
def sourceMap1898 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1898 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1898_checked : acceptsGraphIso
    (source (graph core1898) (root 10) 0 2) DegreeTwoThreeSpectrum3560.graph sourceMap1898=true := by decide +kernel
theorem fusedMap1898_checked : acceptsGraphIso
    (fused (graph core1898) (root 10) 0 2) DegreeTwoThreeSpectrum3564.graph fusedMap1898=true := by decide +kernel
theorem certified1898 : Certified (graph core1898) (root 10) 0 2 :=
  of_native_maps core1898 DegreeTwoThreeSpectrum3560.graph DegreeTwoThreeSpectrum3564.graph
    sourceMap1898 fusedMap1898 sourceMap1898_checked fusedMap1898_checked
    DegreeTwoThreeFiniteComparisons.comparison1898
#print axioms sourceMap1898_checked
#print axioms fusedMap1898_checked
#print axioms certified1898
def sourceMap1898swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1898swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1898swap_checked : acceptsGraphIso
    (source (graph core1898) (root 10) 2 0) DegreeTwoThreeSpectrum3560.graph sourceMap1898swap=true := by decide +kernel
theorem fusedMap1898swap_checked : acceptsGraphIso
    (fused (graph core1898) (root 10) 2 0) DegreeTwoThreeSpectrum3564.graph fusedMap1898swap=true := by decide +kernel
theorem certified1898swap : Certified (graph core1898) (root 10) 2 0 :=
  of_native_maps core1898 DegreeTwoThreeSpectrum3560.graph DegreeTwoThreeSpectrum3564.graph
    sourceMap1898swap fusedMap1898swap sourceMap1898swap_checked fusedMap1898swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1898
#print axioms sourceMap1898swap_checked
#print axioms fusedMap1898swap_checked
#print axioms certified1898swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
