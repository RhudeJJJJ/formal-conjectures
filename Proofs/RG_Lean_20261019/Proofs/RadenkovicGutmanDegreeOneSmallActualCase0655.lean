/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0655 : Family 7 := level7.get ⟨51,by decide⟩
def sourceMap0655 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0655 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0655_checked : acceptsGraphIso
    (source (graph core0655) (root 7) 1 1) DegreeOneSmallSpectrum795.graph sourceMap0655=true := by decide +kernel
theorem fusedMap0655_checked : acceptsGraphIso
    (fused (graph core0655) (root 7) 1 1) DegreeOneSmallSpectrum567.graph fusedMap0655=true := by decide +kernel
theorem certified0655 : Certified (graph core0655) (root 7) 1 1 :=
  of_native_maps core0655 DegreeOneSmallSpectrum795.graph DegreeOneSmallSpectrum567.graph
    sourceMap0655 fusedMap0655 sourceMap0655_checked fusedMap0655_checked
    DegreeOneSmallComparisons.comparison0655
#print axioms sourceMap0655_checked
#print axioms fusedMap0655_checked
#print axioms certified0655
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
