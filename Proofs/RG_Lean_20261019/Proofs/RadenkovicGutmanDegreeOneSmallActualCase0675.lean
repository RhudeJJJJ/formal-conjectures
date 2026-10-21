/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0675 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0675 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 7 0 0 v)
def fusedMap0675 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0675_checked : acceptsGraphIso
    (source (graph core0675) (root 7) 0 0) DegreeOneSmallSpectrum154.graph sourceMap0675=true := by decide +kernel
theorem fusedMap0675_checked : acceptsGraphIso
    (fused (graph core0675) (root 7) 0 0) DegreeOneSmallSpectrum093.graph fusedMap0675=true := by decide +kernel
theorem certified0675 : Certified (graph core0675) (root 7) 0 0 :=
  of_native_maps core0675 DegreeOneSmallSpectrum154.graph DegreeOneSmallSpectrum093.graph
    sourceMap0675 fusedMap0675 sourceMap0675_checked fusedMap0675_checked
    DegreeOneSmallComparisons.comparison0675
#print axioms sourceMap0675_checked
#print axioms fusedMap0675_checked
#print axioms certified0675
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
