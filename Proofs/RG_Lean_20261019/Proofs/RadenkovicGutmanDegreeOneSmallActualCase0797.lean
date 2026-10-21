/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0797 : Family 8 := level8.get ⟨17,by decide⟩
def sourceMap0797 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0797 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0797_checked : acceptsGraphIso
    (source (graph core0797) (root 8) 0 2) DegreeOneSmallSpectrum933.graph sourceMap0797=true := by decide +kernel
theorem fusedMap0797_checked : acceptsGraphIso
    (fused (graph core0797) (root 8) 0 2) DegreeOneSmallSpectrum935.graph fusedMap0797=true := by decide +kernel
theorem certified0797 : Certified (graph core0797) (root 8) 0 2 :=
  of_native_maps core0797 DegreeOneSmallSpectrum933.graph DegreeOneSmallSpectrum935.graph
    sourceMap0797 fusedMap0797 sourceMap0797_checked fusedMap0797_checked
    DegreeOneSmallComparisons.comparison0797
#print axioms sourceMap0797_checked
#print axioms fusedMap0797_checked
#print axioms certified0797
def sourceMap0797swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0797swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0797swap_checked : acceptsGraphIso
    (source (graph core0797) (root 8) 2 0) DegreeOneSmallSpectrum933.graph sourceMap0797swap=true := by decide +kernel
theorem fusedMap0797swap_checked : acceptsGraphIso
    (fused (graph core0797) (root 8) 2 0) DegreeOneSmallSpectrum935.graph fusedMap0797swap=true := by decide +kernel
theorem certified0797swap : Certified (graph core0797) (root 8) 2 0 :=
  of_native_maps core0797 DegreeOneSmallSpectrum933.graph DegreeOneSmallSpectrum935.graph
    sourceMap0797swap fusedMap0797swap sourceMap0797swap_checked fusedMap0797swap_checked
    DegreeOneSmallComparisons.comparison0797
#print axioms sourceMap0797swap_checked
#print axioms fusedMap0797swap_checked
#print axioms certified0797swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
