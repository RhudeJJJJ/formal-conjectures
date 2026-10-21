/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0773 : Family 8 := level8.get ⟨10,by decide⟩
def sourceMap0773 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0773 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0773_checked : acceptsGraphIso
    (source (graph core0773) (root 8) 0 2) DegreeOneSmallSpectrum885.graph sourceMap0773=true := by decide +kernel
theorem fusedMap0773_checked : acceptsGraphIso
    (fused (graph core0773) (root 8) 0 2) DegreeOneSmallSpectrum887.graph fusedMap0773=true := by decide +kernel
theorem certified0773 : Certified (graph core0773) (root 8) 0 2 :=
  of_native_maps core0773 DegreeOneSmallSpectrum885.graph DegreeOneSmallSpectrum887.graph
    sourceMap0773 fusedMap0773 sourceMap0773_checked fusedMap0773_checked
    DegreeOneSmallComparisons.comparison0773
#print axioms sourceMap0773_checked
#print axioms fusedMap0773_checked
#print axioms certified0773
def sourceMap0773swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0773swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0773swap_checked : acceptsGraphIso
    (source (graph core0773) (root 8) 2 0) DegreeOneSmallSpectrum885.graph sourceMap0773swap=true := by decide +kernel
theorem fusedMap0773swap_checked : acceptsGraphIso
    (fused (graph core0773) (root 8) 2 0) DegreeOneSmallSpectrum887.graph fusedMap0773swap=true := by decide +kernel
theorem certified0773swap : Certified (graph core0773) (root 8) 2 0 :=
  of_native_maps core0773 DegreeOneSmallSpectrum885.graph DegreeOneSmallSpectrum887.graph
    sourceMap0773swap fusedMap0773swap sourceMap0773swap_checked fusedMap0773swap_checked
    DegreeOneSmallComparisons.comparison0773
#print axioms sourceMap0773swap_checked
#print axioms fusedMap0773swap_checked
#print axioms certified0773swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
