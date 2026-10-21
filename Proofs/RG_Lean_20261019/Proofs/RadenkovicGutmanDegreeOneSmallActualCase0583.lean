/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0583 : Family 7 := level7.get ⟨30,by decide⟩
def sourceMap0583 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0583 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0583_checked : acceptsGraphIso
    (source (graph core0583) (root 7) 1 1) DegreeOneSmallSpectrum703.graph sourceMap0583=true := by decide +kernel
theorem fusedMap0583_checked : acceptsGraphIso
    (fused (graph core0583) (root 7) 1 1) DegreeOneSmallSpectrum434.graph fusedMap0583=true := by decide +kernel
theorem certified0583 : Certified (graph core0583) (root 7) 1 1 :=
  of_native_maps core0583 DegreeOneSmallSpectrum703.graph DegreeOneSmallSpectrum434.graph
    sourceMap0583 fusedMap0583 sourceMap0583_checked fusedMap0583_checked
    DegreeOneSmallComparisons.comparison0583
#print axioms sourceMap0583_checked
#print axioms fusedMap0583_checked
#print axioms certified0583
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
