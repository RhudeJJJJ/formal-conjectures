/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0377 : Family 9 := level9.get ⟨618,by decide⟩
def sourceMap0377 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0377 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0377_checked : acceptsGraphIso
    (source (graph core0377) (root 9) 0 0) DegreeOneSmallSpectrum760.graph sourceMap0377=true := by decide +kernel
theorem fusedMap0377_checked : acceptsGraphIso
    (fused (graph core0377) (root 9) 0 0) DegreeOneSmallSpectrum759.graph fusedMap0377=true := by decide +kernel
theorem certified0377 : Certified (graph core0377) (root 9) 0 0 :=
  of_native_maps core0377 DegreeOneSmallSpectrum760.graph DegreeOneSmallSpectrum759.graph
    sourceMap0377 fusedMap0377 sourceMap0377_checked fusedMap0377_checked
    DegreeTwoThreeFiniteComparisons.comparison0377
#print axioms sourceMap0377_checked
#print axioms fusedMap0377_checked
#print axioms certified0377
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
