/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0771 : Family 8 := level8.get ⟨10,by decide⟩
def sourceMap0771 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10] (sourceLabel 8 0 0 v)
def fusedMap0771 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0771_checked : acceptsGraphIso
    (source (graph core0771) (root 8) 0 0) DegreeOneSmallSpectrum185.graph sourceMap0771=true := by decide +kernel
theorem fusedMap0771_checked : acceptsGraphIso
    (fused (graph core0771) (root 8) 0 0) DegreeOneSmallSpectrum188.graph fusedMap0771=true := by decide +kernel
theorem certified0771 : Certified (graph core0771) (root 8) 0 0 :=
  of_native_maps core0771 DegreeOneSmallSpectrum185.graph DegreeOneSmallSpectrum188.graph
    sourceMap0771 fusedMap0771 sourceMap0771_checked fusedMap0771_checked
    DegreeOneSmallComparisons.comparison0771
#print axioms sourceMap0771_checked
#print axioms fusedMap0771_checked
#print axioms certified0771
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
