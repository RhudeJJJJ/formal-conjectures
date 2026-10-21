/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0823 : Family 8 := level8.get ⟨26,by decide⟩
def sourceMap0823 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0823 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0823_checked : acceptsGraphIso
    (source (graph core0823) (root 8) 0 0) DegreeOneSmallSpectrum184.graph sourceMap0823=true := by decide +kernel
theorem fusedMap0823_checked : acceptsGraphIso
    (fused (graph core0823) (root 8) 0 0) DegreeOneSmallSpectrum229.graph fusedMap0823=true := by decide +kernel
theorem certified0823 : Certified (graph core0823) (root 8) 0 0 :=
  of_native_maps core0823 DegreeOneSmallSpectrum184.graph DegreeOneSmallSpectrum229.graph
    sourceMap0823 fusedMap0823 sourceMap0823_checked fusedMap0823_checked
    DegreeOneSmallComparisons.comparison0823
#print axioms sourceMap0823_checked
#print axioms fusedMap0823_checked
#print axioms certified0823
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
