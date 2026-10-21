/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0535 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0535 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0535 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0535_checked : acceptsGraphIso
    (source (graph core0535) (root 7) 1 1) DegreeOneSmallSpectrum515.graph sourceMap0535=true := by decide +kernel
theorem fusedMap0535_checked : acceptsGraphIso
    (fused (graph core0535) (root 7) 1 1) DegreeOneSmallSpectrum387.graph fusedMap0535=true := by decide +kernel
theorem certified0535 : Certified (graph core0535) (root 7) 1 1 :=
  of_native_maps core0535 DegreeOneSmallSpectrum515.graph DegreeOneSmallSpectrum387.graph
    sourceMap0535 fusedMap0535 sourceMap0535_checked fusedMap0535_checked
    DegreeOneSmallComparisons.comparison0535
#print axioms sourceMap0535_checked
#print axioms fusedMap0535_checked
#print axioms certified0535
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
