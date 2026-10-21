/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1060 : Family 8 := level8.get ⟨132,by decide⟩
def sourceMap1060 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1060 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1060_checked : acceptsGraphIso
    (source (graph core1060) (root 8) 0 1) DegreeOneSmallSpectrum776.graph sourceMap1060=true := by decide +kernel
theorem fusedMap1060_checked : acceptsGraphIso
    (fused (graph core1060) (root 8) 0 1) DegreeOneSmallSpectrum500.graph fusedMap1060=true := by decide +kernel
theorem certified1060 : Certified (graph core1060) (root 8) 0 1 :=
  of_native_maps core1060 DegreeOneSmallSpectrum776.graph DegreeOneSmallSpectrum500.graph
    sourceMap1060 fusedMap1060 sourceMap1060_checked fusedMap1060_checked
    DegreeOneSmallComparisons.comparison1060
#print axioms sourceMap1060_checked
#print axioms fusedMap1060_checked
#print axioms certified1060
def sourceMap1060swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1060swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1060swap_checked : acceptsGraphIso
    (source (graph core1060) (root 8) 1 0) DegreeOneSmallSpectrum776.graph sourceMap1060swap=true := by decide +kernel
theorem fusedMap1060swap_checked : acceptsGraphIso
    (fused (graph core1060) (root 8) 1 0) DegreeOneSmallSpectrum500.graph fusedMap1060swap=true := by decide +kernel
theorem certified1060swap : Certified (graph core1060) (root 8) 1 0 :=
  of_native_maps core1060 DegreeOneSmallSpectrum776.graph DegreeOneSmallSpectrum500.graph
    sourceMap1060swap fusedMap1060swap sourceMap1060swap_checked fusedMap1060swap_checked
    DegreeOneSmallComparisons.comparison1060
#print axioms sourceMap1060swap_checked
#print axioms fusedMap1060swap_checked
#print axioms certified1060swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
