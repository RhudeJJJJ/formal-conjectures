/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1528 : Family 10 := level10.get ⟨387,by decide⟩
def sourceMap1528 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1528 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1528_checked : acceptsGraphIso
    (source (graph core1528) (root 10) 0 2) DegreeTwoThreeSpectrum2865.graph sourceMap1528=true := by decide +kernel
theorem fusedMap1528_checked : acceptsGraphIso
    (fused (graph core1528) (root 10) 0 2) DegreeTwoThreeSpectrum2870.graph fusedMap1528=true := by decide +kernel
theorem certified1528 : Certified (graph core1528) (root 10) 0 2 :=
  of_native_maps core1528 DegreeTwoThreeSpectrum2865.graph DegreeTwoThreeSpectrum2870.graph
    sourceMap1528 fusedMap1528 sourceMap1528_checked fusedMap1528_checked
    DegreeTwoThreeFiniteComparisons.comparison1528
#print axioms sourceMap1528_checked
#print axioms fusedMap1528_checked
#print axioms certified1528
def sourceMap1528swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1528swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1528swap_checked : acceptsGraphIso
    (source (graph core1528) (root 10) 2 0) DegreeTwoThreeSpectrum2865.graph sourceMap1528swap=true := by decide +kernel
theorem fusedMap1528swap_checked : acceptsGraphIso
    (fused (graph core1528) (root 10) 2 0) DegreeTwoThreeSpectrum2870.graph fusedMap1528swap=true := by decide +kernel
theorem certified1528swap : Certified (graph core1528) (root 10) 2 0 :=
  of_native_maps core1528 DegreeTwoThreeSpectrum2865.graph DegreeTwoThreeSpectrum2870.graph
    sourceMap1528swap fusedMap1528swap sourceMap1528swap_checked fusedMap1528swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1528
#print axioms sourceMap1528swap_checked
#print axioms fusedMap1528swap_checked
#print axioms certified1528swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
