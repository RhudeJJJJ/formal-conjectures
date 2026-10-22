/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0520 : Family 10 := level10.get ⟨460,by decide⟩
def sourceMap0520 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,8,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0520 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0520_checked : acceptsGraphIso
    (source (graph core0520) (root 10) 0 0) DegreeOneSmallSpectrum1017.graph sourceMap0520=true := by decide +kernel
theorem fusedMap0520_checked : acceptsGraphIso
    (fused (graph core0520) (root 10) 0 0) DegreeOneSmallSpectrum1424.graph fusedMap0520=true := by decide +kernel
theorem certified0520 : Certified (graph core0520) (root 10) 0 0 :=
  of_native_maps core0520 DegreeOneSmallSpectrum1017.graph DegreeOneSmallSpectrum1424.graph
    sourceMap0520 fusedMap0520 sourceMap0520_checked fusedMap0520_checked
    DegreeTwoThreeFiniteComparisons.comparison0520
#print axioms sourceMap0520_checked
#print axioms fusedMap0520_checked
#print axioms certified0520
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
