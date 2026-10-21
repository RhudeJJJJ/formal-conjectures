/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0763 : Family 8 := level8.get ⟨8,by decide⟩
def sourceMap0763 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10] (sourceLabel 8 0 0 v)
def fusedMap0763 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0763_checked : acceptsGraphIso
    (source (graph core0763) (root 8) 0 0) DegreeOneSmallSpectrum172.graph sourceMap0763=true := by decide +kernel
theorem fusedMap0763_checked : acceptsGraphIso
    (fused (graph core0763) (root 8) 0 0) DegreeOneSmallSpectrum175.graph fusedMap0763=true := by decide +kernel
theorem certified0763 : Certified (graph core0763) (root 8) 0 0 :=
  of_native_maps core0763 DegreeOneSmallSpectrum172.graph DegreeOneSmallSpectrum175.graph
    sourceMap0763 fusedMap0763 sourceMap0763_checked fusedMap0763_checked
    DegreeOneSmallComparisons.comparison0763
#print axioms sourceMap0763_checked
#print axioms fusedMap0763_checked
#print axioms certified0763
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
