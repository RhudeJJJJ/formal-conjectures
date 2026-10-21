/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0045 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap0045 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap0045 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,4,5,6] (fusedLabel 7 0 0 v)
theorem sourceMap0045_checked : acceptsGraphIso
    (source (graph core0045) (root 7) 0 0) DegreeOneSmallSpectrum115.graph sourceMap0045=true := by decide +kernel
theorem fusedMap0045_checked : acceptsGraphIso
    (fused (graph core0045) (root 7) 0 0) DegreeOneSmallSpectrum111.graph fusedMap0045=true := by decide +kernel
theorem certified0045 : Certified (graph core0045) (root 7) 0 0 :=
  of_native_maps core0045 DegreeOneSmallSpectrum115.graph DegreeOneSmallSpectrum111.graph
    sourceMap0045 fusedMap0045 sourceMap0045_checked fusedMap0045_checked
    DegreeTwoThreeFiniteComparisons.comparison0045
#print axioms sourceMap0045_checked
#print axioms fusedMap0045_checked
#print axioms certified0045
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
