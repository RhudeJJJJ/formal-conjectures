/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0120 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap0120 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0120 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0120_checked : acceptsGraphIso
    (source (graph core0120) (root 8) 0 0) DegreeOneSmallSpectrum224.graph sourceMap0120=true := by decide +kernel
theorem fusedMap0120_checked : acceptsGraphIso
    (fused (graph core0120) (root 8) 0 0) DegreeOneSmallSpectrum221.graph fusedMap0120=true := by decide +kernel
theorem certified0120 : Certified (graph core0120) (root 8) 0 0 :=
  of_native_maps core0120 DegreeOneSmallSpectrum224.graph DegreeOneSmallSpectrum221.graph
    sourceMap0120 fusedMap0120 sourceMap0120_checked fusedMap0120_checked
    DegreeTwoThreeFiniteComparisons.comparison0120
#print axioms sourceMap0120_checked
#print axioms fusedMap0120_checked
#print axioms certified0120
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
