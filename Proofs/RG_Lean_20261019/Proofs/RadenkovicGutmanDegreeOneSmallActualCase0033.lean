/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0033 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0033 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (sourceLabel 2 0 3 v)
def fusedMap0033 : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![1,2,3,0,4,5,6,7] (fusedLabel 2 0 3 v)
theorem sourceMap0033_checked : acceptsGraphIso
    (source (graph core0033) (root 2) 0 3) DegreeOneSmallSpectrum025.graph sourceMap0033=true := by decide +kernel
theorem fusedMap0033_checked : acceptsGraphIso
    (fused (graph core0033) (root 2) 0 3) DegreeOneSmallSpectrum016.graph fusedMap0033=true := by decide +kernel
theorem certified0033 : Certified (graph core0033) (root 2) 0 3 :=
  of_native_maps core0033 DegreeOneSmallSpectrum025.graph DegreeOneSmallSpectrum016.graph
    sourceMap0033 fusedMap0033 sourceMap0033_checked fusedMap0033_checked
    DegreeOneSmallComparisons.comparison0033
#print axioms sourceMap0033_checked
#print axioms fusedMap0033_checked
#print axioms certified0033
def sourceMap0033swap : (Vertices 2 ⊕ Fin 4 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,2,3,0,5,6,7,4] (sourceLabel 2 3 0 v)
def fusedMap0033swap : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![1,2,3,0,4,5,6,7] (fusedLabel 2 3 0 v)
theorem sourceMap0033swap_checked : acceptsGraphIso
    (source (graph core0033) (root 2) 3 0) DegreeOneSmallSpectrum025.graph sourceMap0033swap=true := by decide +kernel
theorem fusedMap0033swap_checked : acceptsGraphIso
    (fused (graph core0033) (root 2) 3 0) DegreeOneSmallSpectrum016.graph fusedMap0033swap=true := by decide +kernel
theorem certified0033swap : Certified (graph core0033) (root 2) 3 0 :=
  of_native_maps core0033 DegreeOneSmallSpectrum025.graph DegreeOneSmallSpectrum016.graph
    sourceMap0033swap fusedMap0033swap sourceMap0033swap_checked fusedMap0033swap_checked
    DegreeOneSmallComparisons.comparison0033
#print axioms sourceMap0033swap_checked
#print axioms fusedMap0033swap_checked
#print axioms certified0033swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
