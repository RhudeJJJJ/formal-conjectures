/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0581 : Family 10 := level10.get ⟨644,by decide⟩
def sourceMap0581 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0581 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0581_checked : acceptsGraphIso
    (source (graph core0581) (root 10) 0 0) DegreeOneSmallSpectrum1633.graph sourceMap0581=true := by decide +kernel
theorem fusedMap0581_checked : acceptsGraphIso
    (fused (graph core0581) (root 10) 0 0) DegreeOneSmallSpectrum1235.graph fusedMap0581=true := by decide +kernel
theorem certified0581 : Certified (graph core0581) (root 10) 0 0 :=
  of_native_maps core0581 DegreeOneSmallSpectrum1633.graph DegreeOneSmallSpectrum1235.graph
    sourceMap0581 fusedMap0581 sourceMap0581_checked fusedMap0581_checked
    DegreeTwoThreeFiniteComparisons.comparison0581
#print axioms sourceMap0581_checked
#print axioms fusedMap0581_checked
#print axioms certified0581
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
