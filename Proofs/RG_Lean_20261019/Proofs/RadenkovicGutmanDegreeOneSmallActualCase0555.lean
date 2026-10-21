/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0555 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0555 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,7,8,9,5,6,3,4] (sourceLabel 7 0 0 v)
def fusedMap0555 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0555_checked : acceptsGraphIso
    (source (graph core0555) (root 7) 0 0) DegreeOneSmallSpectrum115.graph sourceMap0555=true := by decide +kernel
theorem fusedMap0555_checked : acceptsGraphIso
    (fused (graph core0555) (root 7) 0 0) DegreeOneSmallSpectrum088.graph fusedMap0555=true := by decide +kernel
theorem certified0555 : Certified (graph core0555) (root 7) 0 0 :=
  of_native_maps core0555 DegreeOneSmallSpectrum115.graph DegreeOneSmallSpectrum088.graph
    sourceMap0555 fusedMap0555 sourceMap0555_checked fusedMap0555_checked
    DegreeOneSmallComparisons.comparison0555
#print axioms sourceMap0555_checked
#print axioms fusedMap0555_checked
#print axioms certified0555
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
