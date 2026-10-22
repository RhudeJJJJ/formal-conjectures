/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0769 : Family 10 := level10.get ⟨1139,by decide⟩
def sourceMap0769 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0769 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0769_checked : acceptsGraphIso
    (source (graph core0769) (root 10) 0 0) DegreeOneSmallSpectrum1648.graph sourceMap0769=true := by decide +kernel
theorem fusedMap0769_checked : acceptsGraphIso
    (fused (graph core0769) (root 10) 0 0) DegreeOneSmallSpectrum1806.graph fusedMap0769=true := by decide +kernel
theorem certified0769 : Certified (graph core0769) (root 10) 0 0 :=
  of_native_maps core0769 DegreeOneSmallSpectrum1648.graph DegreeOneSmallSpectrum1806.graph
    sourceMap0769 fusedMap0769 sourceMap0769_checked fusedMap0769_checked
    DegreeTwoThreeFiniteComparisons.comparison0769
#print axioms sourceMap0769_checked
#print axioms fusedMap0769_checked
#print axioms certified0769
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
