/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0922 : Family 10 := level10.get ⟨1498,by decide⟩
def sourceMap0922 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0922 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0922_checked : acceptsGraphIso
    (source (graph core0922) (root 10) 0 0) DegreeOneSmallSpectrum1120.graph sourceMap0922=true := by decide +kernel
theorem fusedMap0922_checked : acceptsGraphIso
    (fused (graph core0922) (root 10) 0 0) DegreeOneSmallSpectrum1119.graph fusedMap0922=true := by decide +kernel
theorem certified0922 : Certified (graph core0922) (root 10) 0 0 :=
  of_native_maps core0922 DegreeOneSmallSpectrum1120.graph DegreeOneSmallSpectrum1119.graph
    sourceMap0922 fusedMap0922 sourceMap0922_checked fusedMap0922_checked
    DegreeTwoThreeFiniteComparisons.comparison0922
#print axioms sourceMap0922_checked
#print axioms fusedMap0922_checked
#print axioms certified0922
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
