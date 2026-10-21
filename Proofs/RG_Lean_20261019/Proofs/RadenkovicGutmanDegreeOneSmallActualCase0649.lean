/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0649 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0649 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0649 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0649_checked : acceptsGraphIso
    (source (graph core0649) (root 7) 1 1) DegreeOneSmallSpectrum794.graph sourceMap0649=true := by decide +kernel
theorem fusedMap0649_checked : acceptsGraphIso
    (fused (graph core0649) (root 7) 1 1) DegreeOneSmallSpectrum563.graph fusedMap0649=true := by decide +kernel
theorem certified0649 : Certified (graph core0649) (root 7) 1 1 :=
  of_native_maps core0649 DegreeOneSmallSpectrum794.graph DegreeOneSmallSpectrum563.graph
    sourceMap0649 fusedMap0649 sourceMap0649_checked fusedMap0649_checked
    DegreeOneSmallComparisons.comparison0649
#print axioms sourceMap0649_checked
#print axioms fusedMap0649_checked
#print axioms certified0649
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
