/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0694 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0694 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0694 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0694_checked : acceptsGraphIso
    (source (graph core0694) (root 7) 0 1) DegreeOneSmallSpectrum269.graph sourceMap0694=true := by decide +kernel
theorem fusedMap0694_checked : acceptsGraphIso
    (fused (graph core0694) (root 7) 0 1) DegreeOneSmallSpectrum270.graph fusedMap0694=true := by decide +kernel
theorem certified0694 : Certified (graph core0694) (root 7) 0 1 :=
  of_native_maps core0694 DegreeOneSmallSpectrum269.graph DegreeOneSmallSpectrum270.graph
    sourceMap0694 fusedMap0694 sourceMap0694_checked fusedMap0694_checked
    DegreeOneSmallComparisons.comparison0694
#print axioms sourceMap0694_checked
#print axioms fusedMap0694_checked
#print axioms certified0694
def sourceMap0694swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0694swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0694swap_checked : acceptsGraphIso
    (source (graph core0694) (root 7) 1 0) DegreeOneSmallSpectrum269.graph sourceMap0694swap=true := by decide +kernel
theorem fusedMap0694swap_checked : acceptsGraphIso
    (fused (graph core0694) (root 7) 1 0) DegreeOneSmallSpectrum270.graph fusedMap0694swap=true := by decide +kernel
theorem certified0694swap : Certified (graph core0694) (root 7) 1 0 :=
  of_native_maps core0694 DegreeOneSmallSpectrum269.graph DegreeOneSmallSpectrum270.graph
    sourceMap0694swap fusedMap0694swap sourceMap0694swap_checked fusedMap0694swap_checked
    DegreeOneSmallComparisons.comparison0694
#print axioms sourceMap0694swap_checked
#print axioms fusedMap0694swap_checked
#print axioms certified0694swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
