/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0463 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0463 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 7 1 1 v)
def fusedMap0463 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0463_checked : acceptsGraphIso
    (source (graph core0463) (root 7) 1 1) DegreeOneSmallSpectrum514.graph sourceMap0463=true := by decide +kernel
theorem fusedMap0463_checked : acceptsGraphIso
    (fused (graph core0463) (root 7) 1 1) DegreeOneSmallSpectrum386.graph fusedMap0463=true := by decide +kernel
theorem certified0463 : Certified (graph core0463) (root 7) 1 1 :=
  of_native_maps core0463 DegreeOneSmallSpectrum514.graph DegreeOneSmallSpectrum386.graph
    sourceMap0463 fusedMap0463 sourceMap0463_checked fusedMap0463_checked
    DegreeOneSmallComparisons.comparison0463
#print axioms sourceMap0463_checked
#print axioms fusedMap0463_checked
#print axioms certified0463
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
