/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0940 : Family 8 := level8.get ⟨71,by decide⟩
def sourceMap0940 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0940 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0940_checked : acceptsGraphIso
    (source (graph core0940) (root 8) 0 1) DegreeOneSmallSpectrum553.graph sourceMap0940=true := by decide +kernel
theorem fusedMap0940_checked : acceptsGraphIso
    (fused (graph core0940) (root 8) 0 1) DegreeOneSmallSpectrum567.graph fusedMap0940=true := by decide +kernel
theorem certified0940 : Certified (graph core0940) (root 8) 0 1 :=
  of_native_maps core0940 DegreeOneSmallSpectrum553.graph DegreeOneSmallSpectrum567.graph
    sourceMap0940 fusedMap0940 sourceMap0940_checked fusedMap0940_checked
    DegreeOneSmallComparisons.comparison0940
#print axioms sourceMap0940_checked
#print axioms fusedMap0940_checked
#print axioms certified0940
def sourceMap0940swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0940swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0940swap_checked : acceptsGraphIso
    (source (graph core0940) (root 8) 1 0) DegreeOneSmallSpectrum553.graph sourceMap0940swap=true := by decide +kernel
theorem fusedMap0940swap_checked : acceptsGraphIso
    (fused (graph core0940) (root 8) 1 0) DegreeOneSmallSpectrum567.graph fusedMap0940swap=true := by decide +kernel
theorem certified0940swap : Certified (graph core0940) (root 8) 1 0 :=
  of_native_maps core0940 DegreeOneSmallSpectrum553.graph DegreeOneSmallSpectrum567.graph
    sourceMap0940swap fusedMap0940swap sourceMap0940swap_checked fusedMap0940swap_checked
    DegreeOneSmallComparisons.comparison0940
#print axioms sourceMap0940swap_checked
#print axioms fusedMap0940swap_checked
#print axioms certified0940swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
