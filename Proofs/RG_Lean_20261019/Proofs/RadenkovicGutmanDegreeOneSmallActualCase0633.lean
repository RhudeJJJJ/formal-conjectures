/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0633 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0633 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (sourceLabel 7 0 0 v)
def fusedMap0633 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap0633_checked : acceptsGraphIso
    (source (graph core0633) (root 7) 0 0) DegreeOneSmallSpectrum110.graph sourceMap0633=true := by decide +kernel
theorem fusedMap0633_checked : acceptsGraphIso
    (fused (graph core0633) (root 7) 0 0) DegreeOneSmallSpectrum144.graph fusedMap0633=true := by decide +kernel
theorem certified0633 : Certified (graph core0633) (root 7) 0 0 :=
  of_native_maps core0633 DegreeOneSmallSpectrum110.graph DegreeOneSmallSpectrum144.graph
    sourceMap0633 fusedMap0633 sourceMap0633_checked fusedMap0633_checked
    DegreeOneSmallComparisons.comparison0633
#print axioms sourceMap0633_checked
#print axioms fusedMap0633_checked
#print axioms certified0633
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
