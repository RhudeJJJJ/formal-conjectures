/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0042 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0042 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (sourceLabel 2 1 4 v)
def fusedMap0042 : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![2,3,4,1,0,5,6,7,8,9] (fusedLabel 2 1 4 v)
theorem sourceMap0042_checked : acceptsGraphIso
    (source (graph core0042) (root 2) 1 4) DegreeOneSmallSpectrum081.graph sourceMap0042=true := by decide +kernel
theorem fusedMap0042_checked : acceptsGraphIso
    (fused (graph core0042) (root 2) 1 4) DegreeOneSmallSpectrum073.graph fusedMap0042=true := by decide +kernel
theorem certified0042 : Certified (graph core0042) (root 2) 1 4 :=
  of_native_maps core0042 DegreeOneSmallSpectrum081.graph DegreeOneSmallSpectrum073.graph
    sourceMap0042 fusedMap0042 sourceMap0042_checked fusedMap0042_checked
    DegreeOneSmallComparisons.comparison0042
#print axioms sourceMap0042_checked
#print axioms fusedMap0042_checked
#print axioms certified0042
def sourceMap0042swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,2,3,0,6,7,8,9,4,5] (sourceLabel 2 4 1 v)
def fusedMap0042swap : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![2,3,4,1,0,5,6,7,8,9] (fusedLabel 2 4 1 v)
theorem sourceMap0042swap_checked : acceptsGraphIso
    (source (graph core0042) (root 2) 4 1) DegreeOneSmallSpectrum081.graph sourceMap0042swap=true := by decide +kernel
theorem fusedMap0042swap_checked : acceptsGraphIso
    (fused (graph core0042) (root 2) 4 1) DegreeOneSmallSpectrum073.graph fusedMap0042swap=true := by decide +kernel
theorem certified0042swap : Certified (graph core0042) (root 2) 4 1 :=
  of_native_maps core0042 DegreeOneSmallSpectrum081.graph DegreeOneSmallSpectrum073.graph
    sourceMap0042swap fusedMap0042swap sourceMap0042swap_checked fusedMap0042swap_checked
    DegreeOneSmallComparisons.comparison0042
#print axioms sourceMap0042swap_checked
#print axioms fusedMap0042swap_checked
#print axioms certified0042swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
