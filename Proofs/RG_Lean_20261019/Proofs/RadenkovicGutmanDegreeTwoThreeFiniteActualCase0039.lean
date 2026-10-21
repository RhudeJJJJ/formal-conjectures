/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0039 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap0039 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,5,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0039 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0039_checked : acceptsGraphIso
    (source (graph core0039) (root 7) 0 0) DegreeOneSmallSpectrum100.graph sourceMap0039=true := by decide +kernel
theorem fusedMap0039_checked : acceptsGraphIso
    (fused (graph core0039) (root 7) 0 0) DegreeOneSmallSpectrum143.graph fusedMap0039=true := by decide +kernel
theorem certified0039 : Certified (graph core0039) (root 7) 0 0 :=
  of_native_maps core0039 DegreeOneSmallSpectrum100.graph DegreeOneSmallSpectrum143.graph
    sourceMap0039 fusedMap0039 sourceMap0039_checked fusedMap0039_checked
    DegreeTwoThreeFiniteComparisons.comparison0039
#print axioms sourceMap0039_checked
#print axioms fusedMap0039_checked
#print axioms certified0039
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
