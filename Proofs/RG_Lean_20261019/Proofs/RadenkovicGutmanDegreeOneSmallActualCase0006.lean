/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0006 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0006 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (sourceLabel 1 0 6 v)
def fusedMap0006 : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 0 6 v)
theorem sourceMap0006_checked : acceptsGraphIso
    (source (graph core0006) (root 1) 0 6) DegreeOneSmallSpectrum080.graph sourceMap0006=true := by decide +kernel
theorem fusedMap0006_checked : acceptsGraphIso
    (fused (graph core0006) (root 1) 0 6) DegreeOneSmallSpectrum073.graph fusedMap0006=true := by decide +kernel
theorem certified0006 : Certified (graph core0006) (root 1) 0 6 :=
  of_native_maps core0006 DegreeOneSmallSpectrum080.graph DegreeOneSmallSpectrum073.graph
    sourceMap0006 fusedMap0006 sourceMap0006_checked fusedMap0006_checked
    DegreeOneSmallComparisons.comparison0006
#print axioms sourceMap0006_checked
#print axioms fusedMap0006_checked
#print axioms certified0006
def sourceMap0006swap : (Vertices 1 ⊕ Fin 7 ⊕ Fin 1) → Fin 10 :=
  fun v => ![3,4,2,1,0,6,7,8,9,5] (sourceLabel 1 6 0 v)
def fusedMap0006swap : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 6 0 v)
theorem sourceMap0006swap_checked : acceptsGraphIso
    (source (graph core0006) (root 1) 6 0) DegreeOneSmallSpectrum080.graph sourceMap0006swap=true := by decide +kernel
theorem fusedMap0006swap_checked : acceptsGraphIso
    (fused (graph core0006) (root 1) 6 0) DegreeOneSmallSpectrum073.graph fusedMap0006swap=true := by decide +kernel
theorem certified0006swap : Certified (graph core0006) (root 1) 6 0 :=
  of_native_maps core0006 DegreeOneSmallSpectrum080.graph DegreeOneSmallSpectrum073.graph
    sourceMap0006swap fusedMap0006swap sourceMap0006swap_checked fusedMap0006swap_checked
    DegreeOneSmallComparisons.comparison0006
#print axioms sourceMap0006swap_checked
#print axioms fusedMap0006swap_checked
#print axioms certified0006swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
