/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0651 : Family 7 := level7.get ⟨51,by decide⟩
def sourceMap0651 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,4,5,6,2,3] (sourceLabel 7 0 0 v)
def fusedMap0651 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0651_checked : acceptsGraphIso
    (source (graph core0651) (root 7) 0 0) DegreeOneSmallSpectrum107.graph sourceMap0651=true := by decide +kernel
theorem fusedMap0651_checked : acceptsGraphIso
    (fused (graph core0651) (root 7) 0 0) DegreeOneSmallSpectrum147.graph fusedMap0651=true := by decide +kernel
theorem certified0651 : Certified (graph core0651) (root 7) 0 0 :=
  of_native_maps core0651 DegreeOneSmallSpectrum107.graph DegreeOneSmallSpectrum147.graph
    sourceMap0651 fusedMap0651 sourceMap0651_checked fusedMap0651_checked
    DegreeOneSmallComparisons.comparison0651
#print axioms sourceMap0651_checked
#print axioms fusedMap0651_checked
#print axioms certified0651
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
