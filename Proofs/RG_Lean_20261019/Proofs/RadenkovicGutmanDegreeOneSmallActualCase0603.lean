/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0603 : Family 7 := level7.get ⟨35,by decide⟩
def sourceMap0603 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (sourceLabel 7 0 0 v)
def fusedMap0603 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap0603_checked : acceptsGraphIso
    (source (graph core0603) (root 7) 0 0) DegreeOneSmallSpectrum113.graph sourceMap0603=true := by decide +kernel
theorem fusedMap0603_checked : acceptsGraphIso
    (fused (graph core0603) (root 7) 0 0) DegreeOneSmallSpectrum129.graph fusedMap0603=true := by decide +kernel
theorem certified0603 : Certified (graph core0603) (root 7) 0 0 :=
  of_native_maps core0603 DegreeOneSmallSpectrum113.graph DegreeOneSmallSpectrum129.graph
    sourceMap0603 fusedMap0603 sourceMap0603_checked fusedMap0603_checked
    DegreeOneSmallComparisons.comparison0603
#print axioms sourceMap0603_checked
#print axioms fusedMap0603_checked
#print axioms certified0603
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
