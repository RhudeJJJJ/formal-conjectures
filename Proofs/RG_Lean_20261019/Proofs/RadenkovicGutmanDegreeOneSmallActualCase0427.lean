/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0427 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0427 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0427 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0427_checked : acceptsGraphIso
    (source (graph core0427) (root 6) 1 3) DegreeOneSmallSpectrum1302.graph sourceMap0427=true := by decide +kernel
theorem fusedMap0427_checked : acceptsGraphIso
    (fused (graph core0427) (root 6) 1 3) DegreeOneSmallSpectrum909.graph fusedMap0427=true := by decide +kernel
theorem certified0427 : Certified (graph core0427) (root 6) 1 3 :=
  of_native_maps core0427 DegreeOneSmallSpectrum1302.graph DegreeOneSmallSpectrum909.graph
    sourceMap0427 fusedMap0427 sourceMap0427_checked fusedMap0427_checked
    DegreeOneSmallComparisons.comparison0427
#print axioms sourceMap0427_checked
#print axioms fusedMap0427_checked
#print axioms certified0427
def sourceMap0427swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,7,8] (sourceLabel 6 3 1 v)
def fusedMap0427swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0427swap_checked : acceptsGraphIso
    (source (graph core0427) (root 6) 3 1) DegreeOneSmallSpectrum1302.graph sourceMap0427swap=true := by decide +kernel
theorem fusedMap0427swap_checked : acceptsGraphIso
    (fused (graph core0427) (root 6) 3 1) DegreeOneSmallSpectrum909.graph fusedMap0427swap=true := by decide +kernel
theorem certified0427swap : Certified (graph core0427) (root 6) 3 1 :=
  of_native_maps core0427 DegreeOneSmallSpectrum1302.graph DegreeOneSmallSpectrum909.graph
    sourceMap0427swap fusedMap0427swap sourceMap0427swap_checked fusedMap0427swap_checked
    DegreeOneSmallComparisons.comparison0427
#print axioms sourceMap0427swap_checked
#print axioms fusedMap0427swap_checked
#print axioms certified0427swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
