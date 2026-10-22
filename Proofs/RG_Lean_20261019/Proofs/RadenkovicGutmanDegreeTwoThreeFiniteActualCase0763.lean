/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0763 : Family 10 := level10.get ⟨1122,by decide⟩
def sourceMap0763 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0763 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0763_checked : acceptsGraphIso
    (source (graph core0763) (root 10) 0 0) DegreeOneSmallSpectrum1110.graph sourceMap0763=true := by decide +kernel
theorem fusedMap0763_checked : acceptsGraphIso
    (fused (graph core0763) (root 10) 0 0) DegreeOneSmallSpectrum1109.graph fusedMap0763=true := by decide +kernel
theorem certified0763 : Certified (graph core0763) (root 10) 0 0 :=
  of_native_maps core0763 DegreeOneSmallSpectrum1110.graph DegreeOneSmallSpectrum1109.graph
    sourceMap0763 fusedMap0763 sourceMap0763_checked fusedMap0763_checked
    DegreeTwoThreeFiniteComparisons.comparison0763
#print axioms sourceMap0763_checked
#print axioms fusedMap0763_checked
#print axioms certified0763
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
