/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0826 : Family 8 := level8.get ⟨26,by decide⟩
def sourceMap0826 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0826 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0826_checked : acceptsGraphIso
    (source (graph core0826) (root 8) 1 1) DegreeOneSmallSpectrum1348.graph sourceMap0826=true := by decide +kernel
theorem fusedMap0826_checked : acceptsGraphIso
    (fused (graph core0826) (root 8) 1 1) DegreeOneSmallSpectrum974.graph fusedMap0826=true := by decide +kernel
theorem certified0826 : Certified (graph core0826) (root 8) 1 1 :=
  of_native_maps core0826 DegreeOneSmallSpectrum1348.graph DegreeOneSmallSpectrum974.graph
    sourceMap0826 fusedMap0826 sourceMap0826_checked fusedMap0826_checked
    DegreeOneSmallComparisons.comparison0826
#print axioms sourceMap0826_checked
#print axioms fusedMap0826_checked
#print axioms certified0826
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
