/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0406 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0406 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0406 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0406_checked : acceptsGraphIso
    (source (graph core0406) (root 6) 0 4) DegreeOneSmallSpectrum1101.graph sourceMap0406=true := by decide +kernel
theorem fusedMap0406_checked : acceptsGraphIso
    (fused (graph core0406) (root 6) 0 4) DegreeOneSmallSpectrum871.graph fusedMap0406=true := by decide +kernel
theorem certified0406 : Certified (graph core0406) (root 6) 0 4 :=
  of_native_maps core0406 DegreeOneSmallSpectrum1101.graph DegreeOneSmallSpectrum871.graph
    sourceMap0406 fusedMap0406 sourceMap0406_checked fusedMap0406_checked
    DegreeOneSmallComparisons.comparison0406
#print axioms sourceMap0406_checked
#print axioms fusedMap0406_checked
#print axioms certified0406
def sourceMap0406swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0406swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0406swap_checked : acceptsGraphIso
    (source (graph core0406) (root 6) 4 0) DegreeOneSmallSpectrum1101.graph sourceMap0406swap=true := by decide +kernel
theorem fusedMap0406swap_checked : acceptsGraphIso
    (fused (graph core0406) (root 6) 4 0) DegreeOneSmallSpectrum871.graph fusedMap0406swap=true := by decide +kernel
theorem certified0406swap : Certified (graph core0406) (root 6) 4 0 :=
  of_native_maps core0406 DegreeOneSmallSpectrum1101.graph DegreeOneSmallSpectrum871.graph
    sourceMap0406swap fusedMap0406swap sourceMap0406swap_checked fusedMap0406swap_checked
    DegreeOneSmallComparisons.comparison0406
#print axioms sourceMap0406swap_checked
#print axioms fusedMap0406swap_checked
#print axioms certified0406swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
