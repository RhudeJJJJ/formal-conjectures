/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0699 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0699 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0699 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0699_checked : acceptsGraphIso
    (source (graph core0699) (root 7) 0 0) DegreeOneSmallSpectrum159.graph sourceMap0699=true := by decide +kernel
theorem fusedMap0699_checked : acceptsGraphIso
    (fused (graph core0699) (root 7) 0 0) DegreeOneSmallSpectrum108.graph fusedMap0699=true := by decide +kernel
theorem certified0699 : Certified (graph core0699) (root 7) 0 0 :=
  of_native_maps core0699 DegreeOneSmallSpectrum159.graph DegreeOneSmallSpectrum108.graph
    sourceMap0699 fusedMap0699 sourceMap0699_checked fusedMap0699_checked
    DegreeOneSmallComparisons.comparison0699
#print axioms sourceMap0699_checked
#print axioms fusedMap0699_checked
#print axioms certified0699
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
