/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1658 : Family 9 := level9.get ⟨416,by decide⟩
def sourceMap1658 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1658 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1658_checked : acceptsGraphIso
    (source (graph core1658) (root 9) 0 1) DegreeOneSmallSpectrum1895.graph sourceMap1658=true := by decide +kernel
theorem fusedMap1658_checked : acceptsGraphIso
    (fused (graph core1658) (root 9) 0 1) DegreeOneSmallSpectrum1293.graph fusedMap1658=true := by decide +kernel
theorem certified1658 : Certified (graph core1658) (root 9) 0 1 :=
  of_native_maps core1658 DegreeOneSmallSpectrum1895.graph DegreeOneSmallSpectrum1293.graph
    sourceMap1658 fusedMap1658 sourceMap1658_checked fusedMap1658_checked
    DegreeOneSmallComparisons.comparison1658
#print axioms sourceMap1658_checked
#print axioms fusedMap1658_checked
#print axioms certified1658
def sourceMap1658swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1658swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1658swap_checked : acceptsGraphIso
    (source (graph core1658) (root 9) 1 0) DegreeOneSmallSpectrum1895.graph sourceMap1658swap=true := by decide +kernel
theorem fusedMap1658swap_checked : acceptsGraphIso
    (fused (graph core1658) (root 9) 1 0) DegreeOneSmallSpectrum1293.graph fusedMap1658swap=true := by decide +kernel
theorem certified1658swap : Certified (graph core1658) (root 9) 1 0 :=
  of_native_maps core1658 DegreeOneSmallSpectrum1895.graph DegreeOneSmallSpectrum1293.graph
    sourceMap1658swap fusedMap1658swap sourceMap1658swap_checked fusedMap1658swap_checked
    DegreeOneSmallComparisons.comparison1658
#print axioms sourceMap1658swap_checked
#print axioms fusedMap1658swap_checked
#print axioms certified1658swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
