/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1646 : Family 9 := level9.get ⟨390,by decide⟩
def sourceMap1646 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1646 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1646_checked : acceptsGraphIso
    (source (graph core1646) (root 9) 0 1) DegreeOneSmallSpectrum1871.graph sourceMap1646=true := by decide +kernel
theorem fusedMap1646_checked : acceptsGraphIso
    (fused (graph core1646) (root 9) 0 1) DegreeOneSmallSpectrum1190.graph fusedMap1646=true := by decide +kernel
theorem certified1646 : Certified (graph core1646) (root 9) 0 1 :=
  of_native_maps core1646 DegreeOneSmallSpectrum1871.graph DegreeOneSmallSpectrum1190.graph
    sourceMap1646 fusedMap1646 sourceMap1646_checked fusedMap1646_checked
    DegreeOneSmallComparisons.comparison1646
#print axioms sourceMap1646_checked
#print axioms fusedMap1646_checked
#print axioms certified1646
def sourceMap1646swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1646swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1646swap_checked : acceptsGraphIso
    (source (graph core1646) (root 9) 1 0) DegreeOneSmallSpectrum1871.graph sourceMap1646swap=true := by decide +kernel
theorem fusedMap1646swap_checked : acceptsGraphIso
    (fused (graph core1646) (root 9) 1 0) DegreeOneSmallSpectrum1190.graph fusedMap1646swap=true := by decide +kernel
theorem certified1646swap : Certified (graph core1646) (root 9) 1 0 :=
  of_native_maps core1646 DegreeOneSmallSpectrum1871.graph DegreeOneSmallSpectrum1190.graph
    sourceMap1646swap fusedMap1646swap sourceMap1646swap_checked fusedMap1646swap_checked
    DegreeOneSmallComparisons.comparison1646
#print axioms sourceMap1646swap_checked
#print axioms fusedMap1646swap_checked
#print axioms certified1646swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
