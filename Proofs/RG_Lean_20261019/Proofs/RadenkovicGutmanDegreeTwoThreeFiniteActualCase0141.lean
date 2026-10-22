/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0141 : Family 8 := level8.get ⟨222,by decide⟩
def sourceMap0141 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0141 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0141_checked : acceptsGraphIso
    (source (graph core0141) (root 8) 0 0) DegreeOneSmallSpectrum302.graph sourceMap0141=true := by decide +kernel
theorem fusedMap0141_checked : acceptsGraphIso
    (fused (graph core0141) (root 8) 0 0) DegreeOneSmallSpectrum301.graph fusedMap0141=true := by decide +kernel
theorem certified0141 : Certified (graph core0141) (root 8) 0 0 :=
  of_native_maps core0141 DegreeOneSmallSpectrum302.graph DegreeOneSmallSpectrum301.graph
    sourceMap0141 fusedMap0141 sourceMap0141_checked fusedMap0141_checked
    DegreeTwoThreeFiniteComparisons.comparison0141
#print axioms sourceMap0141_checked
#print axioms fusedMap0141_checked
#print axioms certified0141
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
