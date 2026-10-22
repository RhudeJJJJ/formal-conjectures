/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0761 : Family 10 := level10.get ⟨1119,by decide⟩
def sourceMap0761 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0761 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0761_checked : acceptsGraphIso
    (source (graph core0761) (root 10) 0 0) DegreeOneSmallSpectrum1647.graph sourceMap0761=true := by decide +kernel
theorem fusedMap0761_checked : acceptsGraphIso
    (fused (graph core0761) (root 10) 0 0) DegreeOneSmallSpectrum1769.graph fusedMap0761=true := by decide +kernel
theorem certified0761 : Certified (graph core0761) (root 10) 0 0 :=
  of_native_maps core0761 DegreeOneSmallSpectrum1647.graph DegreeOneSmallSpectrum1769.graph
    sourceMap0761 fusedMap0761 sourceMap0761_checked fusedMap0761_checked
    DegreeTwoThreeFiniteComparisons.comparison0761
#print axioms sourceMap0761_checked
#print axioms fusedMap0761_checked
#print axioms certified0761
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
