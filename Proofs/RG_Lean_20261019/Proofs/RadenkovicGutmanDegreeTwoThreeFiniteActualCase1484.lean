/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1484 : Family 10 := level10.get ⟨237,by decide⟩
def sourceMap1484 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1484 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1484_checked : acceptsGraphIso
    (source (graph core1484) (root 10) 0 2) DegreeTwoThreeSpectrum2554.graph sourceMap1484=true := by decide +kernel
theorem fusedMap1484_checked : acceptsGraphIso
    (fused (graph core1484) (root 10) 0 2) DegreeTwoThreeSpectrum2559.graph fusedMap1484=true := by decide +kernel
theorem certified1484 : Certified (graph core1484) (root 10) 0 2 :=
  of_native_maps core1484 DegreeTwoThreeSpectrum2554.graph DegreeTwoThreeSpectrum2559.graph
    sourceMap1484 fusedMap1484 sourceMap1484_checked fusedMap1484_checked
    DegreeTwoThreeFiniteComparisons.comparison1484
#print axioms sourceMap1484_checked
#print axioms fusedMap1484_checked
#print axioms certified1484
def sourceMap1484swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1484swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1484swap_checked : acceptsGraphIso
    (source (graph core1484) (root 10) 2 0) DegreeTwoThreeSpectrum2554.graph sourceMap1484swap=true := by decide +kernel
theorem fusedMap1484swap_checked : acceptsGraphIso
    (fused (graph core1484) (root 10) 2 0) DegreeTwoThreeSpectrum2559.graph fusedMap1484swap=true := by decide +kernel
theorem certified1484swap : Certified (graph core1484) (root 10) 2 0 :=
  of_native_maps core1484 DegreeTwoThreeSpectrum2554.graph DegreeTwoThreeSpectrum2559.graph
    sourceMap1484swap fusedMap1484swap sourceMap1484swap_checked fusedMap1484swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1484
#print axioms sourceMap1484swap_checked
#print axioms fusedMap1484swap_checked
#print axioms certified1484swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
