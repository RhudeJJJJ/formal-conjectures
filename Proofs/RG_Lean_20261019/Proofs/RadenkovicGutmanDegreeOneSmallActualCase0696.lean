/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0696 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0696 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0696 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0696_checked : acceptsGraphIso
    (source (graph core0696) (root 7) 0 3) DegreeOneSmallSpectrum1084.graph sourceMap0696=true := by decide +kernel
theorem fusedMap0696_checked : acceptsGraphIso
    (fused (graph core0696) (root 7) 0 3) DegreeOneSmallSpectrum1088.graph fusedMap0696=true := by decide +kernel
theorem certified0696 : Certified (graph core0696) (root 7) 0 3 :=
  of_native_maps core0696 DegreeOneSmallSpectrum1084.graph DegreeOneSmallSpectrum1088.graph
    sourceMap0696 fusedMap0696 sourceMap0696_checked fusedMap0696_checked
    DegreeOneSmallComparisons.comparison0696
#print axioms sourceMap0696_checked
#print axioms fusedMap0696_checked
#print axioms certified0696
def sourceMap0696swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0696swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0696swap_checked : acceptsGraphIso
    (source (graph core0696) (root 7) 3 0) DegreeOneSmallSpectrum1084.graph sourceMap0696swap=true := by decide +kernel
theorem fusedMap0696swap_checked : acceptsGraphIso
    (fused (graph core0696) (root 7) 3 0) DegreeOneSmallSpectrum1088.graph fusedMap0696swap=true := by decide +kernel
theorem certified0696swap : Certified (graph core0696) (root 7) 3 0 :=
  of_native_maps core0696 DegreeOneSmallSpectrum1084.graph DegreeOneSmallSpectrum1088.graph
    sourceMap0696swap fusedMap0696swap sourceMap0696swap_checked fusedMap0696swap_checked
    DegreeOneSmallComparisons.comparison0696
#print axioms sourceMap0696swap_checked
#print axioms fusedMap0696swap_checked
#print axioms certified0696swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
