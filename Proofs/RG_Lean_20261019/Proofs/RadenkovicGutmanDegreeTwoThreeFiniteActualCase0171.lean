/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0171 : Family 9 := level9.get ⟨63,by decide⟩
def sourceMap0171 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0171 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0171_checked : acceptsGraphIso
    (source (graph core0171) (root 9) 0 0) DegreeOneSmallSpectrum414.graph sourceMap0171=true := by decide +kernel
theorem fusedMap0171_checked : acceptsGraphIso
    (fused (graph core0171) (root 9) 0 0) DegreeOneSmallSpectrum490.graph fusedMap0171=true := by decide +kernel
theorem certified0171 : Certified (graph core0171) (root 9) 0 0 :=
  of_native_maps core0171 DegreeOneSmallSpectrum414.graph DegreeOneSmallSpectrum490.graph
    sourceMap0171 fusedMap0171 sourceMap0171_checked fusedMap0171_checked
    DegreeTwoThreeFiniteComparisons.comparison0171
#print axioms sourceMap0171_checked
#print axioms fusedMap0171_checked
#print axioms certified0171
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
