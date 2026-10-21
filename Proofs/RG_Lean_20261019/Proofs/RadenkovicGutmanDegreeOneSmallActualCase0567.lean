/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0567 : Family 7 := level7.get ⟨27,by decide⟩
def sourceMap0567 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (sourceLabel 7 0 0 v)
def fusedMap0567 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0567_checked : acceptsGraphIso
    (source (graph core0567) (root 7) 0 0) DegreeOneSmallSpectrum099.graph sourceMap0567=true := by decide +kernel
theorem fusedMap0567_checked : acceptsGraphIso
    (fused (graph core0567) (root 7) 0 0) DegreeOneSmallSpectrum101.graph fusedMap0567=true := by decide +kernel
theorem certified0567 : Certified (graph core0567) (root 7) 0 0 :=
  of_native_maps core0567 DegreeOneSmallSpectrum099.graph DegreeOneSmallSpectrum101.graph
    sourceMap0567 fusedMap0567 sourceMap0567_checked fusedMap0567_checked
    DegreeOneSmallComparisons.comparison0567
#print axioms sourceMap0567_checked
#print axioms fusedMap0567_checked
#print axioms certified0567
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
