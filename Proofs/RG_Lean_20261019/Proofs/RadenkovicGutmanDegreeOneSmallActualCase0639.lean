/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0639 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0639 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (sourceLabel 7 0 0 v)
def fusedMap0639 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap0639_checked : acceptsGraphIso
    (source (graph core0639) (root 7) 0 0) DegreeOneSmallSpectrum114.graph sourceMap0639=true := by decide +kernel
theorem fusedMap0639_checked : acceptsGraphIso
    (fused (graph core0639) (root 7) 0 0) DegreeOneSmallSpectrum145.graph fusedMap0639=true := by decide +kernel
theorem certified0639 : Certified (graph core0639) (root 7) 0 0 :=
  of_native_maps core0639 DegreeOneSmallSpectrum114.graph DegreeOneSmallSpectrum145.graph
    sourceMap0639 fusedMap0639 sourceMap0639_checked fusedMap0639_checked
    DegreeOneSmallComparisons.comparison0639
#print axioms sourceMap0639_checked
#print axioms fusedMap0639_checked
#print axioms certified0639
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
