/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0048 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0048 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,5,6,2,3,4,0,7,8,9,10] (sourceLabel 2 2 4 v)
def fusedMap0048 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 2 4 v)
theorem sourceMap0048_checked : acceptsGraphIso
    (source (graph core0048) (root 2) 2 4) DegreeOneSmallSpectrum222.graph sourceMap0048=true := by decide +kernel
theorem fusedMap0048_checked : acceptsGraphIso
    (fused (graph core0048) (root 2) 2 4) DegreeOneSmallSpectrum168.graph fusedMap0048=true := by decide +kernel
theorem certified0048 : Certified (graph core0048) (root 2) 2 4 :=
  of_native_maps core0048 DegreeOneSmallSpectrum222.graph DegreeOneSmallSpectrum168.graph
    sourceMap0048 fusedMap0048 sourceMap0048_checked fusedMap0048_checked
    DegreeOneSmallComparisons.comparison0048
#print axioms sourceMap0048_checked
#print axioms fusedMap0048_checked
#print axioms certified0048
def sourceMap0048swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,5,6,0,7,8,9,10,2,3,4] (sourceLabel 2 4 2 v)
def fusedMap0048swap : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 4 2 v)
theorem sourceMap0048swap_checked : acceptsGraphIso
    (source (graph core0048) (root 2) 4 2) DegreeOneSmallSpectrum222.graph sourceMap0048swap=true := by decide +kernel
theorem fusedMap0048swap_checked : acceptsGraphIso
    (fused (graph core0048) (root 2) 4 2) DegreeOneSmallSpectrum168.graph fusedMap0048swap=true := by decide +kernel
theorem certified0048swap : Certified (graph core0048) (root 2) 4 2 :=
  of_native_maps core0048 DegreeOneSmallSpectrum222.graph DegreeOneSmallSpectrum168.graph
    sourceMap0048swap fusedMap0048swap sourceMap0048swap_checked fusedMap0048swap_checked
    DegreeOneSmallComparisons.comparison0048
#print axioms sourceMap0048swap_checked
#print axioms fusedMap0048swap_checked
#print axioms certified0048swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
