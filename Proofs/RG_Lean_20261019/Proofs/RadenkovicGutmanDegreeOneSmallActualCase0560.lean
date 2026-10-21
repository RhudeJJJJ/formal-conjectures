/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0560 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0560 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0560 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0560_checked : acceptsGraphIso
    (source (graph core0560) (root 7) 1 2) DegreeOneSmallSpectrum1491.graph sourceMap0560=true := by decide +kernel
theorem fusedMap0560_checked : acceptsGraphIso
    (fused (graph core0560) (root 7) 1 2) DegreeOneSmallSpectrum974.graph fusedMap0560=true := by decide +kernel
theorem certified0560 : Certified (graph core0560) (root 7) 1 2 :=
  of_native_maps core0560 DegreeOneSmallSpectrum1491.graph DegreeOneSmallSpectrum974.graph
    sourceMap0560 fusedMap0560 sourceMap0560_checked fusedMap0560_checked
    DegreeOneSmallComparisons.comparison0560
#print axioms sourceMap0560_checked
#print axioms fusedMap0560_checked
#print axioms certified0560
def sourceMap0560swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0560swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0560swap_checked : acceptsGraphIso
    (source (graph core0560) (root 7) 2 1) DegreeOneSmallSpectrum1491.graph sourceMap0560swap=true := by decide +kernel
theorem fusedMap0560swap_checked : acceptsGraphIso
    (fused (graph core0560) (root 7) 2 1) DegreeOneSmallSpectrum974.graph fusedMap0560swap=true := by decide +kernel
theorem certified0560swap : Certified (graph core0560) (root 7) 2 1 :=
  of_native_maps core0560 DegreeOneSmallSpectrum1491.graph DegreeOneSmallSpectrum974.graph
    sourceMap0560swap fusedMap0560swap sourceMap0560swap_checked fusedMap0560swap_checked
    DegreeOneSmallComparisons.comparison0560
#print axioms sourceMap0560swap_checked
#print axioms fusedMap0560swap_checked
#print axioms certified0560swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
