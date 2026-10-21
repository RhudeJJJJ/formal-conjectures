/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0035 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0035 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (sourceLabel 2 0 5 v)
def fusedMap0035 : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![2,3,4,1,0,5,6,7,8,9] (fusedLabel 2 0 5 v)
theorem sourceMap0035_checked : acceptsGraphIso
    (source (graph core0035) (root 2) 0 5) DegreeOneSmallSpectrum086.graph sourceMap0035=true := by decide +kernel
theorem fusedMap0035_checked : acceptsGraphIso
    (fused (graph core0035) (root 2) 0 5) DegreeOneSmallSpectrum073.graph fusedMap0035=true := by decide +kernel
theorem certified0035 : Certified (graph core0035) (root 2) 0 5 :=
  of_native_maps core0035 DegreeOneSmallSpectrum086.graph DegreeOneSmallSpectrum073.graph
    sourceMap0035 fusedMap0035 sourceMap0035_checked fusedMap0035_checked
    DegreeOneSmallComparisons.comparison0035
#print axioms sourceMap0035_checked
#print axioms fusedMap0035_checked
#print axioms certified0035
def sourceMap0035swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,3,4,1,0,6,7,8,9,5] (sourceLabel 2 5 0 v)
def fusedMap0035swap : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![2,3,4,1,0,5,6,7,8,9] (fusedLabel 2 5 0 v)
theorem sourceMap0035swap_checked : acceptsGraphIso
    (source (graph core0035) (root 2) 5 0) DegreeOneSmallSpectrum086.graph sourceMap0035swap=true := by decide +kernel
theorem fusedMap0035swap_checked : acceptsGraphIso
    (fused (graph core0035) (root 2) 5 0) DegreeOneSmallSpectrum073.graph fusedMap0035swap=true := by decide +kernel
theorem certified0035swap : Certified (graph core0035) (root 2) 5 0 :=
  of_native_maps core0035 DegreeOneSmallSpectrum086.graph DegreeOneSmallSpectrum073.graph
    sourceMap0035swap fusedMap0035swap sourceMap0035swap_checked fusedMap0035swap_checked
    DegreeOneSmallComparisons.comparison0035
#print axioms sourceMap0035swap_checked
#print axioms fusedMap0035swap_checked
#print axioms certified0035swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
