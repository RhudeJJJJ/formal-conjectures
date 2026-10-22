/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0163 : Family 9 := level9.get ⟨28,by decide⟩
def sourceMap0163 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0163 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0163_checked : acceptsGraphIso
    (source (graph core0163) (root 9) 0 0) DegreeOneSmallSpectrum426.graph sourceMap0163=true := by decide +kernel
theorem fusedMap0163_checked : acceptsGraphIso
    (fused (graph core0163) (root 9) 0 0) DegreeOneSmallSpectrum384.graph fusedMap0163=true := by decide +kernel
theorem certified0163 : Certified (graph core0163) (root 9) 0 0 :=
  of_native_maps core0163 DegreeOneSmallSpectrum426.graph DegreeOneSmallSpectrum384.graph
    sourceMap0163 fusedMap0163 sourceMap0163_checked fusedMap0163_checked
    DegreeTwoThreeFiniteComparisons.comparison0163
#print axioms sourceMap0163_checked
#print axioms fusedMap0163_checked
#print axioms certified0163
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
