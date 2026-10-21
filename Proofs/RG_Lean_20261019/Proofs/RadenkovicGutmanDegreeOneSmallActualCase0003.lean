/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0003 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0003 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (sourceLabel 1 0 3 v)
def fusedMap0003 : (Vertices 1 ⊕ Fin 5) → Fin 7 :=
  fun v => ![2,3,1,0,4,5,6] (fusedLabel 1 0 3 v)
theorem sourceMap0003_checked : acceptsGraphIso
    (source (graph core0003) (root 1) 0 3) DegreeOneSmallSpectrum008.graph sourceMap0003=true := by decide +kernel
theorem fusedMap0003_checked : acceptsGraphIso
    (fused (graph core0003) (root 1) 0 3) DegreeOneSmallSpectrum010.graph fusedMap0003=true := by decide +kernel
theorem certified0003 : Certified (graph core0003) (root 1) 0 3 :=
  of_native_maps core0003 DegreeOneSmallSpectrum008.graph DegreeOneSmallSpectrum010.graph
    sourceMap0003 fusedMap0003 sourceMap0003_checked fusedMap0003_checked
    DegreeOneSmallComparisons.comparison0003
#print axioms sourceMap0003_checked
#print axioms fusedMap0003_checked
#print axioms certified0003
def sourceMap0003swap : (Vertices 1 ⊕ Fin 4 ⊕ Fin 1) → Fin 7 :=
  fun v => ![1,2,0,4,5,6,3] (sourceLabel 1 3 0 v)
def fusedMap0003swap : (Vertices 1 ⊕ Fin 5) → Fin 7 :=
  fun v => ![2,3,1,0,4,5,6] (fusedLabel 1 3 0 v)
theorem sourceMap0003swap_checked : acceptsGraphIso
    (source (graph core0003) (root 1) 3 0) DegreeOneSmallSpectrum008.graph sourceMap0003swap=true := by decide +kernel
theorem fusedMap0003swap_checked : acceptsGraphIso
    (fused (graph core0003) (root 1) 3 0) DegreeOneSmallSpectrum010.graph fusedMap0003swap=true := by decide +kernel
theorem certified0003swap : Certified (graph core0003) (root 1) 3 0 :=
  of_native_maps core0003 DegreeOneSmallSpectrum008.graph DegreeOneSmallSpectrum010.graph
    sourceMap0003swap fusedMap0003swap sourceMap0003swap_checked fusedMap0003swap_checked
    DegreeOneSmallComparisons.comparison0003
#print axioms sourceMap0003swap_checked
#print axioms fusedMap0003swap_checked
#print axioms certified0003swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
