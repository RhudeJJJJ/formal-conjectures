/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0034 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap0034 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0034 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0034_checked : acceptsGraphIso
    (source (graph core0034) (root 7) 0 0) DegreeOneSmallSpectrum102.graph sourceMap0034=true := by decide +kernel
theorem fusedMap0034_checked : acceptsGraphIso
    (fused (graph core0034) (root 7) 0 0) DegreeOneSmallSpectrum120.graph fusedMap0034=true := by decide +kernel
theorem certified0034 : Certified (graph core0034) (root 7) 0 0 :=
  of_native_maps core0034 DegreeOneSmallSpectrum102.graph DegreeOneSmallSpectrum120.graph
    sourceMap0034 fusedMap0034 sourceMap0034_checked fusedMap0034_checked
    DegreeTwoThreeFiniteComparisons.comparison0034
#print axioms sourceMap0034_checked
#print axioms fusedMap0034_checked
#print axioms certified0034
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
