/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0813 : Family 8 := level8.get ⟨22,by decide⟩
def sourceMap0813 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0813 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0813_checked : acceptsGraphIso
    (source (graph core0813) (root 8) 0 2) DegreeOneSmallSpectrum959.graph sourceMap0813=true := by decide +kernel
theorem fusedMap0813_checked : acceptsGraphIso
    (fused (graph core0813) (root 8) 0 2) DegreeOneSmallSpectrum961.graph fusedMap0813=true := by decide +kernel
theorem certified0813 : Certified (graph core0813) (root 8) 0 2 :=
  of_native_maps core0813 DegreeOneSmallSpectrum959.graph DegreeOneSmallSpectrum961.graph
    sourceMap0813 fusedMap0813 sourceMap0813_checked fusedMap0813_checked
    DegreeOneSmallComparisons.comparison0813
#print axioms sourceMap0813_checked
#print axioms fusedMap0813_checked
#print axioms certified0813
def sourceMap0813swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0813swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0813swap_checked : acceptsGraphIso
    (source (graph core0813) (root 8) 2 0) DegreeOneSmallSpectrum959.graph sourceMap0813swap=true := by decide +kernel
theorem fusedMap0813swap_checked : acceptsGraphIso
    (fused (graph core0813) (root 8) 2 0) DegreeOneSmallSpectrum961.graph fusedMap0813swap=true := by decide +kernel
theorem certified0813swap : Certified (graph core0813) (root 8) 2 0 :=
  of_native_maps core0813 DegreeOneSmallSpectrum959.graph DegreeOneSmallSpectrum961.graph
    sourceMap0813swap fusedMap0813swap sourceMap0813swap_checked fusedMap0813swap_checked
    DegreeOneSmallComparisons.comparison0813
#print axioms sourceMap0813swap_checked
#print axioms fusedMap0813swap_checked
#print axioms certified0813swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
