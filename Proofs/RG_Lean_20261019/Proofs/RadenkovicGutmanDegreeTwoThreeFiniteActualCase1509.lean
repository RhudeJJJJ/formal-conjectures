/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1509 : Family 10 := level10.get ⟨321,by decide⟩
def sourceMap1509 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1509 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1509_checked : acceptsGraphIso
    (source (graph core1509) (root 10) 0 2) DegreeTwoThreeSpectrum2723.graph sourceMap1509=true := by decide +kernel
theorem fusedMap1509_checked : acceptsGraphIso
    (fused (graph core1509) (root 10) 0 2) DegreeTwoThreeSpectrum2728.graph fusedMap1509=true := by decide +kernel
theorem certified1509 : Certified (graph core1509) (root 10) 0 2 :=
  of_native_maps core1509 DegreeTwoThreeSpectrum2723.graph DegreeTwoThreeSpectrum2728.graph
    sourceMap1509 fusedMap1509 sourceMap1509_checked fusedMap1509_checked
    DegreeTwoThreeFiniteComparisons.comparison1509
#print axioms sourceMap1509_checked
#print axioms fusedMap1509_checked
#print axioms certified1509
def sourceMap1509swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1509swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1509swap_checked : acceptsGraphIso
    (source (graph core1509) (root 10) 2 0) DegreeTwoThreeSpectrum2723.graph sourceMap1509swap=true := by decide +kernel
theorem fusedMap1509swap_checked : acceptsGraphIso
    (fused (graph core1509) (root 10) 2 0) DegreeTwoThreeSpectrum2728.graph fusedMap1509swap=true := by decide +kernel
theorem certified1509swap : Certified (graph core1509) (root 10) 2 0 :=
  of_native_maps core1509 DegreeTwoThreeSpectrum2723.graph DegreeTwoThreeSpectrum2728.graph
    sourceMap1509swap fusedMap1509swap sourceMap1509swap_checked fusedMap1509swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1509
#print axioms sourceMap1509swap_checked
#print axioms fusedMap1509swap_checked
#print axioms certified1509swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
