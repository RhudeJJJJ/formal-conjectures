/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1940 : Family 10 := level10.get ⟨1463,by decide⟩
def sourceMap1940 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,4,5,6,7,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1940 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1940_checked : acceptsGraphIso
    (source (graph core1940) (root 10) 0 2) DegreeTwoThreeSpectrum3657.graph sourceMap1940=true := by decide +kernel
theorem fusedMap1940_checked : acceptsGraphIso
    (fused (graph core1940) (root 10) 0 2) DegreeTwoThreeSpectrum3700.graph fusedMap1940=true := by decide +kernel
theorem certified1940 : Certified (graph core1940) (root 10) 0 2 :=
  of_native_maps core1940 DegreeTwoThreeSpectrum3657.graph DegreeTwoThreeSpectrum3700.graph
    sourceMap1940 fusedMap1940 sourceMap1940_checked fusedMap1940_checked
    DegreeTwoThreeFiniteComparisons.comparison1940
#print axioms sourceMap1940_checked
#print axioms fusedMap1940_checked
#print axioms certified1940
def sourceMap1940swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,4,5,6,1,2,3,7] (sourceLabel 10 2 0 v)
def fusedMap1940swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1940swap_checked : acceptsGraphIso
    (source (graph core1940) (root 10) 2 0) DegreeTwoThreeSpectrum3657.graph sourceMap1940swap=true := by decide +kernel
theorem fusedMap1940swap_checked : acceptsGraphIso
    (fused (graph core1940) (root 10) 2 0) DegreeTwoThreeSpectrum3700.graph fusedMap1940swap=true := by decide +kernel
theorem certified1940swap : Certified (graph core1940) (root 10) 2 0 :=
  of_native_maps core1940 DegreeTwoThreeSpectrum3657.graph DegreeTwoThreeSpectrum3700.graph
    sourceMap1940swap fusedMap1940swap sourceMap1940swap_checked fusedMap1940swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1940
#print axioms sourceMap1940swap_checked
#print axioms fusedMap1940swap_checked
#print axioms certified1940swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
