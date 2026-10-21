/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0886 : Family 8 := level8.get ⟨48,by decide⟩
def sourceMap0886 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,11,12,7,8,9,10] (sourceLabel 8 1 1 v)
def fusedMap0886 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0886_checked : acceptsGraphIso
    (source (graph core0886) (root 8) 1 1) DegreeOneSmallSpectrum1254.graph sourceMap0886=true := by decide +kernel
theorem fusedMap0886_checked : acceptsGraphIso
    (fused (graph core0886) (root 8) 1 1) DegreeOneSmallSpectrum888.graph fusedMap0886=true := by decide +kernel
theorem certified0886 : Certified (graph core0886) (root 8) 1 1 :=
  of_native_maps core0886 DegreeOneSmallSpectrum1254.graph DegreeOneSmallSpectrum888.graph
    sourceMap0886 fusedMap0886 sourceMap0886_checked fusedMap0886_checked
    DegreeOneSmallComparisons.comparison0886
#print axioms sourceMap0886_checked
#print axioms fusedMap0886_checked
#print axioms certified0886
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
