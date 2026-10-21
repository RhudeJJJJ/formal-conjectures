/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0211 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0211 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0211 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0211_checked : acceptsGraphIso
    (source (graph core0211) (root 5) 0 4) DegreeOneSmallSpectrum417.graph sourceMap0211=true := by decide +kernel
theorem fusedMap0211_checked : acceptsGraphIso
    (fused (graph core0211) (root 5) 0 4) DegreeOneSmallSpectrum370.graph fusedMap0211=true := by decide +kernel
theorem certified0211 : Certified (graph core0211) (root 5) 0 4 :=
  of_native_maps core0211 DegreeOneSmallSpectrum417.graph DegreeOneSmallSpectrum370.graph
    sourceMap0211 fusedMap0211 sourceMap0211_checked fusedMap0211_checked
    DegreeOneSmallComparisons.comparison0211
#print axioms sourceMap0211_checked
#print axioms fusedMap0211_checked
#print axioms certified0211
def sourceMap0211swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap0211swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0211swap_checked : acceptsGraphIso
    (source (graph core0211) (root 5) 4 0) DegreeOneSmallSpectrum417.graph sourceMap0211swap=true := by decide +kernel
theorem fusedMap0211swap_checked : acceptsGraphIso
    (fused (graph core0211) (root 5) 4 0) DegreeOneSmallSpectrum370.graph fusedMap0211swap=true := by decide +kernel
theorem certified0211swap : Certified (graph core0211) (root 5) 4 0 :=
  of_native_maps core0211 DegreeOneSmallSpectrum417.graph DegreeOneSmallSpectrum370.graph
    sourceMap0211swap fusedMap0211swap sourceMap0211swap_checked fusedMap0211swap_checked
    DegreeOneSmallComparisons.comparison0211
#print axioms sourceMap0211swap_checked
#print axioms fusedMap0211swap_checked
#print axioms certified0211swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
