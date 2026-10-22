/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0646 : Family 10 := level10.get ⟨821,by decide⟩
def sourceMap0646 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0646 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0646_checked : acceptsGraphIso
    (source (graph core0646) (root 10) 0 0) DegreeOneSmallSpectrum942.graph sourceMap0646=true := by decide +kernel
theorem fusedMap0646_checked : acceptsGraphIso
    (fused (graph core0646) (root 10) 0 0) DegreeOneSmallSpectrum941.graph fusedMap0646=true := by decide +kernel
theorem certified0646 : Certified (graph core0646) (root 10) 0 0 :=
  of_native_maps core0646 DegreeOneSmallSpectrum942.graph DegreeOneSmallSpectrum941.graph
    sourceMap0646 fusedMap0646 sourceMap0646_checked fusedMap0646_checked
    DegreeTwoThreeFiniteComparisons.comparison0646
#print axioms sourceMap0646_checked
#print axioms fusedMap0646_checked
#print axioms certified0646
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
