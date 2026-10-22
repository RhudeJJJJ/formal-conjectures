/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1494 : Family 10 := level10.get ⟨270,by decide⟩
def sourceMap1494 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1494 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1494_checked : acceptsGraphIso
    (source (graph core1494) (root 10) 0 2) DegreeTwoThreeSpectrum2619.graph sourceMap1494=true := by decide +kernel
theorem fusedMap1494_checked : acceptsGraphIso
    (fused (graph core1494) (root 10) 0 2) DegreeTwoThreeSpectrum2624.graph fusedMap1494=true := by decide +kernel
theorem certified1494 : Certified (graph core1494) (root 10) 0 2 :=
  of_native_maps core1494 DegreeTwoThreeSpectrum2619.graph DegreeTwoThreeSpectrum2624.graph
    sourceMap1494 fusedMap1494 sourceMap1494_checked fusedMap1494_checked
    DegreeTwoThreeFiniteComparisons.comparison1494
#print axioms sourceMap1494_checked
#print axioms fusedMap1494_checked
#print axioms certified1494
def sourceMap1494swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1494swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1494swap_checked : acceptsGraphIso
    (source (graph core1494) (root 10) 2 0) DegreeTwoThreeSpectrum2619.graph sourceMap1494swap=true := by decide +kernel
theorem fusedMap1494swap_checked : acceptsGraphIso
    (fused (graph core1494) (root 10) 2 0) DegreeTwoThreeSpectrum2624.graph fusedMap1494swap=true := by decide +kernel
theorem certified1494swap : Certified (graph core1494) (root 10) 2 0 :=
  of_native_maps core1494 DegreeTwoThreeSpectrum2619.graph DegreeTwoThreeSpectrum2624.graph
    sourceMap1494swap fusedMap1494swap sourceMap1494swap_checked fusedMap1494swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1494
#print axioms sourceMap1494swap_checked
#print axioms fusedMap1494swap_checked
#print axioms certified1494swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
