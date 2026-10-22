/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0501 : Family 10 := level10.get ⟨401,by decide⟩
def sourceMap0501 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0501 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0501_checked : acceptsGraphIso
    (source (graph core0501) (root 10) 0 0) DegreeOneSmallSpectrum1390.graph sourceMap0501=true := by decide +kernel
theorem fusedMap0501_checked : acceptsGraphIso
    (fused (graph core0501) (root 10) 0 0) DegreeOneSmallSpectrum1345.graph fusedMap0501=true := by decide +kernel
theorem certified0501 : Certified (graph core0501) (root 10) 0 0 :=
  of_native_maps core0501 DegreeOneSmallSpectrum1390.graph DegreeOneSmallSpectrum1345.graph
    sourceMap0501 fusedMap0501 sourceMap0501_checked fusedMap0501_checked
    DegreeTwoThreeFiniteComparisons.comparison0501
#print axioms sourceMap0501_checked
#print axioms fusedMap0501_checked
#print axioms certified0501
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
