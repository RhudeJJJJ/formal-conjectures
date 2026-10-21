/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0922 : Family 8 := level8.get ⟨62,by decide⟩
def sourceMap0922 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0922 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0922_checked : acceptsGraphIso
    (source (graph core0922) (root 8) 1 1) DegreeOneSmallSpectrum1337.graph sourceMap0922=true := by decide +kernel
theorem fusedMap0922_checked : acceptsGraphIso
    (fused (graph core0922) (root 8) 1 1) DegreeOneSmallSpectrum924.graph fusedMap0922=true := by decide +kernel
theorem certified0922 : Certified (graph core0922) (root 8) 1 1 :=
  of_native_maps core0922 DegreeOneSmallSpectrum1337.graph DegreeOneSmallSpectrum924.graph
    sourceMap0922 fusedMap0922 sourceMap0922_checked fusedMap0922_checked
    DegreeOneSmallComparisons.comparison0922
#print axioms sourceMap0922_checked
#print axioms fusedMap0922_checked
#print axioms certified0922
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
