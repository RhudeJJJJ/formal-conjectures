/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1955 : Family 10 := level10.get ⟨1502,by decide⟩
def sourceMap1955 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1955 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1955_checked : acceptsGraphIso
    (source (graph core1955) (root 10) 0 2) DegreeTwoThreeSpectrum3402.graph sourceMap1955=true := by decide +kernel
theorem fusedMap1955_checked : acceptsGraphIso
    (fused (graph core1955) (root 10) 0 2) DegreeTwoThreeSpectrum3727.graph fusedMap1955=true := by decide +kernel
theorem certified1955 : Certified (graph core1955) (root 10) 0 2 :=
  of_native_maps core1955 DegreeTwoThreeSpectrum3402.graph DegreeTwoThreeSpectrum3727.graph
    sourceMap1955 fusedMap1955 sourceMap1955_checked fusedMap1955_checked
    DegreeTwoThreeFiniteComparisons.comparison1955
#print axioms sourceMap1955_checked
#print axioms fusedMap1955_checked
#print axioms certified1955
def sourceMap1955swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1955swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1955swap_checked : acceptsGraphIso
    (source (graph core1955) (root 10) 2 0) DegreeTwoThreeSpectrum3402.graph sourceMap1955swap=true := by decide +kernel
theorem fusedMap1955swap_checked : acceptsGraphIso
    (fused (graph core1955) (root 10) 2 0) DegreeTwoThreeSpectrum3727.graph fusedMap1955swap=true := by decide +kernel
theorem certified1955swap : Certified (graph core1955) (root 10) 2 0 :=
  of_native_maps core1955 DegreeTwoThreeSpectrum3402.graph DegreeTwoThreeSpectrum3727.graph
    sourceMap1955swap fusedMap1955swap sourceMap1955swap_checked fusedMap1955swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1955
#print axioms sourceMap1955swap_checked
#print axioms fusedMap1955swap_checked
#print axioms certified1955swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
