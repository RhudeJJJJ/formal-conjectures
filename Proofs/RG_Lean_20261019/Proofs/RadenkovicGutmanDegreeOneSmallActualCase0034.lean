/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0034 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0034 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (sourceLabel 2 0 4 v)
def fusedMap0034 : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 0 4 v)
theorem sourceMap0034_checked : acceptsGraphIso
    (source (graph core0034) (root 2) 0 4) DegreeOneSmallSpectrum035.graph sourceMap0034=true := by decide +kernel
theorem fusedMap0034_checked : acceptsGraphIso
    (fused (graph core0034) (root 2) 0 4) DegreeOneSmallSpectrum037.graph fusedMap0034=true := by decide +kernel
theorem certified0034 : Certified (graph core0034) (root 2) 0 4 :=
  of_native_maps core0034 DegreeOneSmallSpectrum035.graph DegreeOneSmallSpectrum037.graph
    sourceMap0034 fusedMap0034 sourceMap0034_checked fusedMap0034_checked
    DegreeOneSmallComparisons.comparison0034
#print axioms sourceMap0034_checked
#print axioms fusedMap0034_checked
#print axioms certified0034
def sourceMap0034swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,2,3,0,5,6,7,8,4] (sourceLabel 2 4 0 v)
def fusedMap0034swap : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 4 0 v)
theorem sourceMap0034swap_checked : acceptsGraphIso
    (source (graph core0034) (root 2) 4 0) DegreeOneSmallSpectrum035.graph sourceMap0034swap=true := by decide +kernel
theorem fusedMap0034swap_checked : acceptsGraphIso
    (fused (graph core0034) (root 2) 4 0) DegreeOneSmallSpectrum037.graph fusedMap0034swap=true := by decide +kernel
theorem certified0034swap : Certified (graph core0034) (root 2) 4 0 :=
  of_native_maps core0034 DegreeOneSmallSpectrum035.graph DegreeOneSmallSpectrum037.graph
    sourceMap0034swap fusedMap0034swap sourceMap0034swap_checked fusedMap0034swap_checked
    DegreeOneSmallComparisons.comparison0034
#print axioms sourceMap0034swap_checked
#print axioms fusedMap0034swap_checked
#print axioms certified0034swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
