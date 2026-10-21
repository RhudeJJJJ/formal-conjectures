/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0228 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0228 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0228 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0228_checked : acceptsGraphIso
    (source (graph core0228) (root 5) 1 4) DegreeOneSmallSpectrum1142.graph sourceMap0228=true := by decide +kernel
theorem fusedMap0228_checked : acceptsGraphIso
    (fused (graph core0228) (root 5) 1 4) DegreeOneSmallSpectrum879.graph fusedMap0228=true := by decide +kernel
theorem certified0228 : Certified (graph core0228) (root 5) 1 4 :=
  of_native_maps core0228 DegreeOneSmallSpectrum1142.graph DegreeOneSmallSpectrum879.graph
    sourceMap0228 fusedMap0228 sourceMap0228_checked fusedMap0228_checked
    DegreeOneSmallComparisons.comparison0228
#print axioms sourceMap0228_checked
#print axioms fusedMap0228_checked
#print axioms certified0228
def sourceMap0228swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap0228swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0228swap_checked : acceptsGraphIso
    (source (graph core0228) (root 5) 4 1) DegreeOneSmallSpectrum1142.graph sourceMap0228swap=true := by decide +kernel
theorem fusedMap0228swap_checked : acceptsGraphIso
    (fused (graph core0228) (root 5) 4 1) DegreeOneSmallSpectrum879.graph fusedMap0228swap=true := by decide +kernel
theorem certified0228swap : Certified (graph core0228) (root 5) 4 1 :=
  of_native_maps core0228 DegreeOneSmallSpectrum1142.graph DegreeOneSmallSpectrum879.graph
    sourceMap0228swap fusedMap0228swap sourceMap0228swap_checked fusedMap0228swap_checked
    DegreeOneSmallComparisons.comparison0228
#print axioms sourceMap0228swap_checked
#print axioms fusedMap0228swap_checked
#print axioms certified0228swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
