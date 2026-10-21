/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0513 : Family 7 := level7.get ⟨13,by decide⟩
def sourceMap0513 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0513 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0513_checked : acceptsGraphIso
    (source (graph core0513) (root 7) 0 0) DegreeOneSmallSpectrum126.graph sourceMap0513=true := by decide +kernel
theorem fusedMap0513_checked : acceptsGraphIso
    (fused (graph core0513) (root 7) 0 0) DegreeOneSmallSpectrum082.graph fusedMap0513=true := by decide +kernel
theorem certified0513 : Certified (graph core0513) (root 7) 0 0 :=
  of_native_maps core0513 DegreeOneSmallSpectrum126.graph DegreeOneSmallSpectrum082.graph
    sourceMap0513 fusedMap0513 sourceMap0513_checked fusedMap0513_checked
    DegreeOneSmallComparisons.comparison0513
#print axioms sourceMap0513_checked
#print axioms fusedMap0513_checked
#print axioms certified0513
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
