/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1724 : Family 9 := level9.get ⟨542,by decide⟩
def sourceMap1724 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1724 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1724_checked : acceptsGraphIso
    (source (graph core1724) (root 9) 0 1) DegreeOneSmallSpectrum1520.graph sourceMap1724=true := by decide +kernel
theorem fusedMap1724_checked : acceptsGraphIso
    (fused (graph core1724) (root 9) 0 1) DegreeOneSmallSpectrum1521.graph fusedMap1724=true := by decide +kernel
theorem certified1724 : Certified (graph core1724) (root 9) 0 1 :=
  of_native_maps core1724 DegreeOneSmallSpectrum1520.graph DegreeOneSmallSpectrum1521.graph
    sourceMap1724 fusedMap1724 sourceMap1724_checked fusedMap1724_checked
    DegreeOneSmallComparisons.comparison1724
#print axioms sourceMap1724_checked
#print axioms fusedMap1724_checked
#print axioms certified1724
def sourceMap1724swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1724swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1724swap_checked : acceptsGraphIso
    (source (graph core1724) (root 9) 1 0) DegreeOneSmallSpectrum1520.graph sourceMap1724swap=true := by decide +kernel
theorem fusedMap1724swap_checked : acceptsGraphIso
    (fused (graph core1724) (root 9) 1 0) DegreeOneSmallSpectrum1521.graph fusedMap1724swap=true := by decide +kernel
theorem certified1724swap : Certified (graph core1724) (root 9) 1 0 :=
  of_native_maps core1724 DegreeOneSmallSpectrum1520.graph DegreeOneSmallSpectrum1521.graph
    sourceMap1724swap fusedMap1724swap sourceMap1724swap_checked fusedMap1724swap_checked
    DegreeOneSmallComparisons.comparison1724
#print axioms sourceMap1724swap_checked
#print axioms fusedMap1724swap_checked
#print axioms certified1724swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
