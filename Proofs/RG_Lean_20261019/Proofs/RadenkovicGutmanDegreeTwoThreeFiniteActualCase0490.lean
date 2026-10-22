/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0490 : Family 10 := level10.get ⟨363,by decide⟩
def sourceMap0490 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0490 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0490_checked : acceptsGraphIso
    (source (graph core0490) (root 10) 0 0) DegreeOneSmallSpectrum938.graph sourceMap0490=true := by decide +kernel
theorem fusedMap0490_checked : acceptsGraphIso
    (fused (graph core0490) (root 10) 0 0) DegreeOneSmallSpectrum937.graph fusedMap0490=true := by decide +kernel
theorem certified0490 : Certified (graph core0490) (root 10) 0 0 :=
  of_native_maps core0490 DegreeOneSmallSpectrum938.graph DegreeOneSmallSpectrum937.graph
    sourceMap0490 fusedMap0490 sourceMap0490_checked fusedMap0490_checked
    DegreeTwoThreeFiniteComparisons.comparison0490
#print axioms sourceMap0490_checked
#print axioms fusedMap0490_checked
#print axioms certified0490
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
