/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0698 : Family 10 := level10.get ⟨955,by decide⟩
def sourceMap0698 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,7,8,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0698 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,7,8,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0698_checked : acceptsGraphIso
    (source (graph core0698) (root 10) 0 0) DegreeOneSmallSpectrum1119.graph sourceMap0698=true := by decide +kernel
theorem fusedMap0698_checked : acceptsGraphIso
    (fused (graph core0698) (root 10) 0 0) DegreeOneSmallSpectrum1096.graph fusedMap0698=true := by decide +kernel
theorem certified0698 : Certified (graph core0698) (root 10) 0 0 :=
  of_native_maps core0698 DegreeOneSmallSpectrum1119.graph DegreeOneSmallSpectrum1096.graph
    sourceMap0698 fusedMap0698 sourceMap0698_checked fusedMap0698_checked
    DegreeTwoThreeFiniteComparisons.comparison0698
#print axioms sourceMap0698_checked
#print axioms fusedMap0698_checked
#print axioms certified0698
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
