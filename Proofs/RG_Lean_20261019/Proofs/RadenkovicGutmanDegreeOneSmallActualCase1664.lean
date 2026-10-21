/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1664 : Family 9 := level9.get ⟨421,by decide⟩
def sourceMap1664 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1664 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1664_checked : acceptsGraphIso
    (source (graph core1664) (root 9) 0 1) DegreeOneSmallSpectrum1909.graph sourceMap1664=true := by decide +kernel
theorem fusedMap1664_checked : acceptsGraphIso
    (fused (graph core1664) (root 9) 0 1) DegreeOneSmallSpectrum1302.graph fusedMap1664=true := by decide +kernel
theorem certified1664 : Certified (graph core1664) (root 9) 0 1 :=
  of_native_maps core1664 DegreeOneSmallSpectrum1909.graph DegreeOneSmallSpectrum1302.graph
    sourceMap1664 fusedMap1664 sourceMap1664_checked fusedMap1664_checked
    DegreeOneSmallComparisons.comparison1664
#print axioms sourceMap1664_checked
#print axioms fusedMap1664_checked
#print axioms certified1664
def sourceMap1664swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1664swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1664swap_checked : acceptsGraphIso
    (source (graph core1664) (root 9) 1 0) DegreeOneSmallSpectrum1909.graph sourceMap1664swap=true := by decide +kernel
theorem fusedMap1664swap_checked : acceptsGraphIso
    (fused (graph core1664) (root 9) 1 0) DegreeOneSmallSpectrum1302.graph fusedMap1664swap=true := by decide +kernel
theorem certified1664swap : Certified (graph core1664) (root 9) 1 0 :=
  of_native_maps core1664 DegreeOneSmallSpectrum1909.graph DegreeOneSmallSpectrum1302.graph
    sourceMap1664swap fusedMap1664swap sourceMap1664swap_checked fusedMap1664swap_checked
    DegreeOneSmallComparisons.comparison1664
#print axioms sourceMap1664swap_checked
#print axioms fusedMap1664swap_checked
#print axioms certified1664swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
