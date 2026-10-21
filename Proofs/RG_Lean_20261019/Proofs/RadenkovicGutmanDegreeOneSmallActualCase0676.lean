/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0676 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0676 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0676 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0676_checked : acceptsGraphIso
    (source (graph core0676) (root 7) 0 1) DegreeOneSmallSpectrum238.graph sourceMap0676=true := by decide +kernel
theorem fusedMap0676_checked : acceptsGraphIso
    (fused (graph core0676) (root 7) 0 1) DegreeOneSmallSpectrum239.graph fusedMap0676=true := by decide +kernel
theorem certified0676 : Certified (graph core0676) (root 7) 0 1 :=
  of_native_maps core0676 DegreeOneSmallSpectrum238.graph DegreeOneSmallSpectrum239.graph
    sourceMap0676 fusedMap0676 sourceMap0676_checked fusedMap0676_checked
    DegreeOneSmallComparisons.comparison0676
#print axioms sourceMap0676_checked
#print axioms fusedMap0676_checked
#print axioms certified0676
def sourceMap0676swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0676swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0676swap_checked : acceptsGraphIso
    (source (graph core0676) (root 7) 1 0) DegreeOneSmallSpectrum238.graph sourceMap0676swap=true := by decide +kernel
theorem fusedMap0676swap_checked : acceptsGraphIso
    (fused (graph core0676) (root 7) 1 0) DegreeOneSmallSpectrum239.graph fusedMap0676swap=true := by decide +kernel
theorem certified0676swap : Certified (graph core0676) (root 7) 1 0 :=
  of_native_maps core0676 DegreeOneSmallSpectrum238.graph DegreeOneSmallSpectrum239.graph
    sourceMap0676swap fusedMap0676swap sourceMap0676swap_checked fusedMap0676swap_checked
    DegreeOneSmallComparisons.comparison0676
#print axioms sourceMap0676swap_checked
#print axioms fusedMap0676swap_checked
#print axioms certified0676swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
