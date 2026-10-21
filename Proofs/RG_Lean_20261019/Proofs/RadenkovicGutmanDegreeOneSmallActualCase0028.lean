/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0028 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0028 : (Vertices 1 ⊕ Fin 5 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,11,1,2,3,4,5,6,7,8,9,10] (sourceLabel 1 4 4 v)
def fusedMap0028 : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 4 4 v)
theorem sourceMap0028_checked : acceptsGraphIso
    (source (graph core0028) (root 1) 4 4) DegreeOneSmallSpectrum397.graph sourceMap0028=true := by decide +kernel
theorem fusedMap0028_checked : acceptsGraphIso
    (fused (graph core0028) (root 1) 4 4) DegreeOneSmallSpectrum369.graph fusedMap0028=true := by decide +kernel
theorem certified0028 : Certified (graph core0028) (root 1) 4 4 :=
  of_native_maps core0028 DegreeOneSmallSpectrum397.graph DegreeOneSmallSpectrum369.graph
    sourceMap0028 fusedMap0028 sourceMap0028_checked fusedMap0028_checked
    DegreeOneSmallComparisons.comparison0028
#print axioms sourceMap0028_checked
#print axioms fusedMap0028_checked
#print axioms certified0028
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
