/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0619 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0619 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0619 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0619_checked : acceptsGraphIso
    (source (graph core0619) (root 7) 1 1) DegreeOneSmallSpectrum788.graph sourceMap0619=true := by decide +kernel
theorem fusedMap0619_checked : acceptsGraphIso
    (fused (graph core0619) (root 7) 1 1) DegreeOneSmallSpectrum510.graph fusedMap0619=true := by decide +kernel
theorem certified0619 : Certified (graph core0619) (root 7) 1 1 :=
  of_native_maps core0619 DegreeOneSmallSpectrum788.graph DegreeOneSmallSpectrum510.graph
    sourceMap0619 fusedMap0619 sourceMap0619_checked fusedMap0619_checked
    DegreeOneSmallComparisons.comparison0619
#print axioms sourceMap0619_checked
#print axioms fusedMap0619_checked
#print axioms certified0619
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
