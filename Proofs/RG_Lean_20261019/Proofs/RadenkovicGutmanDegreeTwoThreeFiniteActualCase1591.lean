/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1591 : Family 10 := level10.get ⟨575,by decide⟩
def sourceMap1591 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1591 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1591_checked : acceptsGraphIso
    (source (graph core1591) (root 10) 0 2) DegreeTwoThreeSpectrum3201.graph sourceMap1591=true := by decide +kernel
theorem fusedMap1591_checked : acceptsGraphIso
    (fused (graph core1591) (root 10) 0 2) DegreeTwoThreeSpectrum2518.graph fusedMap1591=true := by decide +kernel
theorem certified1591 : Certified (graph core1591) (root 10) 0 2 :=
  of_native_maps core1591 DegreeTwoThreeSpectrum3201.graph DegreeTwoThreeSpectrum2518.graph
    sourceMap1591 fusedMap1591 sourceMap1591_checked fusedMap1591_checked
    DegreeTwoThreeFiniteComparisons.comparison1591
#print axioms sourceMap1591_checked
#print axioms fusedMap1591_checked
#print axioms certified1591
def sourceMap1591swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1591swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1591swap_checked : acceptsGraphIso
    (source (graph core1591) (root 10) 2 0) DegreeTwoThreeSpectrum3201.graph sourceMap1591swap=true := by decide +kernel
theorem fusedMap1591swap_checked : acceptsGraphIso
    (fused (graph core1591) (root 10) 2 0) DegreeTwoThreeSpectrum2518.graph fusedMap1591swap=true := by decide +kernel
theorem certified1591swap : Certified (graph core1591) (root 10) 2 0 :=
  of_native_maps core1591 DegreeTwoThreeSpectrum3201.graph DegreeTwoThreeSpectrum2518.graph
    sourceMap1591swap fusedMap1591swap sourceMap1591swap_checked fusedMap1591swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1591
#print axioms sourceMap1591swap_checked
#print axioms fusedMap1591swap_checked
#print axioms certified1591swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
