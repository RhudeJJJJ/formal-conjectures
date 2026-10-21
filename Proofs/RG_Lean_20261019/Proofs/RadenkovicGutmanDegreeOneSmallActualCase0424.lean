/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0424 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0424 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0424 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0424_checked : acceptsGraphIso
    (source (graph core0424) (root 6) 0 4) DegreeOneSmallSpectrum1306.graph sourceMap0424=true := by decide +kernel
theorem fusedMap0424_checked : acceptsGraphIso
    (fused (graph core0424) (root 6) 0 4) DegreeOneSmallSpectrum909.graph fusedMap0424=true := by decide +kernel
theorem certified0424 : Certified (graph core0424) (root 6) 0 4 :=
  of_native_maps core0424 DegreeOneSmallSpectrum1306.graph DegreeOneSmallSpectrum909.graph
    sourceMap0424 fusedMap0424 sourceMap0424_checked fusedMap0424_checked
    DegreeOneSmallComparisons.comparison0424
#print axioms sourceMap0424_checked
#print axioms fusedMap0424_checked
#print axioms certified0424
def sourceMap0424swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap0424swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0424swap_checked : acceptsGraphIso
    (source (graph core0424) (root 6) 4 0) DegreeOneSmallSpectrum1306.graph sourceMap0424swap=true := by decide +kernel
theorem fusedMap0424swap_checked : acceptsGraphIso
    (fused (graph core0424) (root 6) 4 0) DegreeOneSmallSpectrum909.graph fusedMap0424swap=true := by decide +kernel
theorem certified0424swap : Certified (graph core0424) (root 6) 4 0 :=
  of_native_maps core0424 DegreeOneSmallSpectrum1306.graph DegreeOneSmallSpectrum909.graph
    sourceMap0424swap fusedMap0424swap sourceMap0424swap_checked fusedMap0424swap_checked
    DegreeOneSmallComparisons.comparison0424
#print axioms sourceMap0424swap_checked
#print axioms fusedMap0424swap_checked
#print axioms certified0424swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
