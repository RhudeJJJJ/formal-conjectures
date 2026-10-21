/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0586 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0586 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0586 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0586_checked : acceptsGraphIso
    (source (graph core0586) (root 7) 0 1) DegreeOneSmallSpectrum290.graph sourceMap0586=true := by decide +kernel
theorem fusedMap0586_checked : acceptsGraphIso
    (fused (graph core0586) (root 7) 0 1) DegreeOneSmallSpectrum177.graph fusedMap0586=true := by decide +kernel
theorem certified0586 : Certified (graph core0586) (root 7) 0 1 :=
  of_native_maps core0586 DegreeOneSmallSpectrum290.graph DegreeOneSmallSpectrum177.graph
    sourceMap0586 fusedMap0586 sourceMap0586_checked fusedMap0586_checked
    DegreeOneSmallComparisons.comparison0586
#print axioms sourceMap0586_checked
#print axioms fusedMap0586_checked
#print axioms certified0586
def sourceMap0586swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0586swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0586swap_checked : acceptsGraphIso
    (source (graph core0586) (root 7) 1 0) DegreeOneSmallSpectrum290.graph sourceMap0586swap=true := by decide +kernel
theorem fusedMap0586swap_checked : acceptsGraphIso
    (fused (graph core0586) (root 7) 1 0) DegreeOneSmallSpectrum177.graph fusedMap0586swap=true := by decide +kernel
theorem certified0586swap : Certified (graph core0586) (root 7) 1 0 :=
  of_native_maps core0586 DegreeOneSmallSpectrum290.graph DegreeOneSmallSpectrum177.graph
    sourceMap0586swap fusedMap0586swap sourceMap0586swap_checked fusedMap0586swap_checked
    DegreeOneSmallComparisons.comparison0586
#print axioms sourceMap0586swap_checked
#print axioms fusedMap0586swap_checked
#print axioms certified0586swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
