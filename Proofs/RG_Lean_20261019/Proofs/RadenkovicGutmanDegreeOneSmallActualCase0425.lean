/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0425 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0425 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0425 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0425_checked : acceptsGraphIso
    (source (graph core0425) (root 6) 1 1) DegreeOneSmallSpectrum322.graph sourceMap0425=true := by decide +kernel
theorem fusedMap0425_checked : acceptsGraphIso
    (fused (graph core0425) (root 6) 1 1) DegreeOneSmallSpectrum198.graph fusedMap0425=true := by decide +kernel
theorem certified0425 : Certified (graph core0425) (root 6) 1 1 :=
  of_native_maps core0425 DegreeOneSmallSpectrum322.graph DegreeOneSmallSpectrum198.graph
    sourceMap0425 fusedMap0425 sourceMap0425_checked fusedMap0425_checked
    DegreeOneSmallComparisons.comparison0425
#print axioms sourceMap0425_checked
#print axioms fusedMap0425_checked
#print axioms certified0425
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
