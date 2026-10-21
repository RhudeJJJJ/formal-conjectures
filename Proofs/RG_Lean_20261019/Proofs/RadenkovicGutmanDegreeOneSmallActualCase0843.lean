/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0843 : Family 8 := level8.get ⟨35,by decide⟩
def sourceMap0843 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap0843 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0843_checked : acceptsGraphIso
    (source (graph core0843) (root 8) 0 0) DegreeOneSmallSpectrum255.graph sourceMap0843=true := by decide +kernel
theorem fusedMap0843_checked : acceptsGraphIso
    (fused (graph core0843) (root 8) 0 0) DegreeOneSmallSpectrum170.graph fusedMap0843=true := by decide +kernel
theorem certified0843 : Certified (graph core0843) (root 8) 0 0 :=
  of_native_maps core0843 DegreeOneSmallSpectrum255.graph DegreeOneSmallSpectrum170.graph
    sourceMap0843 fusedMap0843 sourceMap0843_checked fusedMap0843_checked
    DegreeOneSmallComparisons.comparison0843
#print axioms sourceMap0843_checked
#print axioms fusedMap0843_checked
#print axioms certified0843
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
