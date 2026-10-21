/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0459 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0459 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0459 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0459_checked : acceptsGraphIso
    (source (graph core0459) (root 7) 0 0) DegreeOneSmallSpectrum078.graph sourceMap0459=true := by decide +kernel
theorem fusedMap0459_checked : acceptsGraphIso
    (fused (graph core0459) (root 7) 0 0) DegreeOneSmallSpectrum086.graph fusedMap0459=true := by decide +kernel
theorem certified0459 : Certified (graph core0459) (root 7) 0 0 :=
  of_native_maps core0459 DegreeOneSmallSpectrum078.graph DegreeOneSmallSpectrum086.graph
    sourceMap0459 fusedMap0459 sourceMap0459_checked fusedMap0459_checked
    DegreeOneSmallComparisons.comparison0459
#print axioms sourceMap0459_checked
#print axioms fusedMap0459_checked
#print axioms certified0459
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
