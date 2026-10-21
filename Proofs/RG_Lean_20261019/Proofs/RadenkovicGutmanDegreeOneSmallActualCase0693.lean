/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0693 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0693 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0693 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0693_checked : acceptsGraphIso
    (source (graph core0693) (root 7) 0 0) DegreeOneSmallSpectrum158.graph sourceMap0693=true := by decide +kernel
theorem fusedMap0693_checked : acceptsGraphIso
    (fused (graph core0693) (root 7) 0 0) DegreeOneSmallSpectrum107.graph fusedMap0693=true := by decide +kernel
theorem certified0693 : Certified (graph core0693) (root 7) 0 0 :=
  of_native_maps core0693 DegreeOneSmallSpectrum158.graph DegreeOneSmallSpectrum107.graph
    sourceMap0693 fusedMap0693 sourceMap0693_checked fusedMap0693_checked
    DegreeOneSmallComparisons.comparison0693
#print axioms sourceMap0693_checked
#print axioms fusedMap0693_checked
#print axioms certified0693
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
