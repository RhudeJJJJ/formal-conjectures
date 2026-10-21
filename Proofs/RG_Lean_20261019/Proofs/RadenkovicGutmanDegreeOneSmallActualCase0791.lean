/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0791 : Family 8 := level8.get ⟨16,by decide⟩
def sourceMap0791 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0791 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0791_checked : acceptsGraphIso
    (source (graph core0791) (root 8) 0 0) DegreeOneSmallSpectrum192.graph sourceMap0791=true := by decide +kernel
theorem fusedMap0791_checked : acceptsGraphIso
    (fused (graph core0791) (root 8) 0 0) DegreeOneSmallSpectrum212.graph fusedMap0791=true := by decide +kernel
theorem certified0791 : Certified (graph core0791) (root 8) 0 0 :=
  of_native_maps core0791 DegreeOneSmallSpectrum192.graph DegreeOneSmallSpectrum212.graph
    sourceMap0791 fusedMap0791 sourceMap0791_checked fusedMap0791_checked
    DegreeOneSmallComparisons.comparison0791
#print axioms sourceMap0791_checked
#print axioms fusedMap0791_checked
#print axioms certified0791
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
