/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0886 : Family 10 := level10.get ⟨1414,by decide⟩
def sourceMap0886 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0886 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0886_checked : acceptsGraphIso
    (source (graph core0886) (root 10) 0 0) DegreeOneSmallSpectrum1807.graph sourceMap0886=true := by decide +kernel
theorem fusedMap0886_checked : acceptsGraphIso
    (fused (graph core0886) (root 10) 0 0) DegreeOneSmallSpectrum1770.graph fusedMap0886=true := by decide +kernel
theorem certified0886 : Certified (graph core0886) (root 10) 0 0 :=
  of_native_maps core0886 DegreeOneSmallSpectrum1807.graph DegreeOneSmallSpectrum1770.graph
    sourceMap0886 fusedMap0886 sourceMap0886_checked fusedMap0886_checked
    DegreeTwoThreeFiniteComparisons.comparison0886
#print axioms sourceMap0886_checked
#print axioms fusedMap0886_checked
#print axioms certified0886
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
