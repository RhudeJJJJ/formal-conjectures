/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0569 : Family 10 := level10.get ⟨608,by decide⟩
def sourceMap0569 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0569 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0569_checked : acceptsGraphIso
    (source (graph core0569) (root 10) 0 0) DegreeOneSmallSpectrum1649.graph sourceMap0569=true := by decide +kernel
theorem fusedMap0569_checked : acceptsGraphIso
    (fused (graph core0569) (root 10) 0 0) DegreeOneSmallSpectrum1171.graph fusedMap0569=true := by decide +kernel
theorem certified0569 : Certified (graph core0569) (root 10) 0 0 :=
  of_native_maps core0569 DegreeOneSmallSpectrum1649.graph DegreeOneSmallSpectrum1171.graph
    sourceMap0569 fusedMap0569 sourceMap0569_checked fusedMap0569_checked
    DegreeTwoThreeFiniteComparisons.comparison0569
#print axioms sourceMap0569_checked
#print axioms fusedMap0569_checked
#print axioms certified0569
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
