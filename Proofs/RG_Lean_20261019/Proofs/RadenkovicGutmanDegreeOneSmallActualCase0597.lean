/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0597 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0597 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (sourceLabel 7 0 0 v)
def fusedMap0597 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap0597_checked : acceptsGraphIso
    (source (graph core0597) (root 7) 0 0) DegreeOneSmallSpectrum109.graph sourceMap0597=true := by decide +kernel
theorem fusedMap0597_checked : acceptsGraphIso
    (fused (graph core0597) (root 7) 0 0) DegreeOneSmallSpectrum128.graph fusedMap0597=true := by decide +kernel
theorem certified0597 : Certified (graph core0597) (root 7) 0 0 :=
  of_native_maps core0597 DegreeOneSmallSpectrum109.graph DegreeOneSmallSpectrum128.graph
    sourceMap0597 fusedMap0597 sourceMap0597_checked fusedMap0597_checked
    DegreeOneSmallComparisons.comparison0597
#print axioms sourceMap0597_checked
#print axioms fusedMap0597_checked
#print axioms certified0597
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
