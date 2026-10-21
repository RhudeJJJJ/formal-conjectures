/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0014 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0014 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,5,3,4,1,0,6,7,8,9] (sourceLabel 1 1 5 v)
def fusedMap0014 : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 1 5 v)
theorem sourceMap0014_checked : acceptsGraphIso
    (source (graph core0014) (root 1) 1 5) DegreeOneSmallSpectrum086.graph sourceMap0014=true := by decide +kernel
theorem fusedMap0014_checked : acceptsGraphIso
    (fused (graph core0014) (root 1) 1 5) DegreeOneSmallSpectrum073.graph fusedMap0014=true := by decide +kernel
theorem certified0014 : Certified (graph core0014) (root 1) 1 5 :=
  of_native_maps core0014 DegreeOneSmallSpectrum086.graph DegreeOneSmallSpectrum073.graph
    sourceMap0014 fusedMap0014 sourceMap0014_checked fusedMap0014_checked
    DegreeOneSmallComparisons.comparison0014
#print axioms sourceMap0014_checked
#print axioms fusedMap0014_checked
#print axioms certified0014
def sourceMap0014swap : (Vertices 1 ⊕ Fin 6 ⊕ Fin 2) → Fin 10 :=
  fun v => ![2,5,1,0,6,7,8,9,3,4] (sourceLabel 1 5 1 v)
def fusedMap0014swap : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 5 1 v)
theorem sourceMap0014swap_checked : acceptsGraphIso
    (source (graph core0014) (root 1) 5 1) DegreeOneSmallSpectrum086.graph sourceMap0014swap=true := by decide +kernel
theorem fusedMap0014swap_checked : acceptsGraphIso
    (fused (graph core0014) (root 1) 5 1) DegreeOneSmallSpectrum073.graph fusedMap0014swap=true := by decide +kernel
theorem certified0014swap : Certified (graph core0014) (root 1) 5 1 :=
  of_native_maps core0014 DegreeOneSmallSpectrum086.graph DegreeOneSmallSpectrum073.graph
    sourceMap0014swap fusedMap0014swap sourceMap0014swap_checked fusedMap0014swap_checked
    DegreeOneSmallComparisons.comparison0014
#print axioms sourceMap0014swap_checked
#print axioms fusedMap0014swap_checked
#print axioms certified0014swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
