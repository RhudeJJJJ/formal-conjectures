/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0959 : Family 8 := level8.get ⟨78,by decide⟩
def sourceMap0959 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0959 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0959_checked : acceptsGraphIso
    (source (graph core0959) (root 8) 0 0) DegreeOneSmallSpectrum281.graph sourceMap0959=true := by decide +kernel
theorem fusedMap0959_checked : acceptsGraphIso
    (fused (graph core0959) (root 8) 0 0) DegreeOneSmallSpectrum221.graph fusedMap0959=true := by decide +kernel
theorem certified0959 : Certified (graph core0959) (root 8) 0 0 :=
  of_native_maps core0959 DegreeOneSmallSpectrum281.graph DegreeOneSmallSpectrum221.graph
    sourceMap0959 fusedMap0959 sourceMap0959_checked fusedMap0959_checked
    DegreeOneSmallComparisons.comparison0959
#print axioms sourceMap0959_checked
#print axioms fusedMap0959_checked
#print axioms certified0959
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
