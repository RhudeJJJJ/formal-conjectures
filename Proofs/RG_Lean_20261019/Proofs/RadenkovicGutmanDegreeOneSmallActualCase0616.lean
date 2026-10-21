/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0616 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0616 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (sourceLabel 7 0 1 v)
def fusedMap0616 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0616_checked : acceptsGraphIso
    (source (graph core0616) (root 7) 0 1) DegreeOneSmallSpectrum328.graph sourceMap0616=true := by decide +kernel
theorem fusedMap0616_checked : acceptsGraphIso
    (fused (graph core0616) (root 7) 0 1) DegreeOneSmallSpectrum199.graph fusedMap0616=true := by decide +kernel
theorem certified0616 : Certified (graph core0616) (root 7) 0 1 :=
  of_native_maps core0616 DegreeOneSmallSpectrum328.graph DegreeOneSmallSpectrum199.graph
    sourceMap0616 fusedMap0616 sourceMap0616_checked fusedMap0616_checked
    DegreeOneSmallComparisons.comparison0616
#print axioms sourceMap0616_checked
#print axioms fusedMap0616_checked
#print axioms certified0616
def sourceMap0616swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 7 1 0 v)
def fusedMap0616swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0616swap_checked : acceptsGraphIso
    (source (graph core0616) (root 7) 1 0) DegreeOneSmallSpectrum328.graph sourceMap0616swap=true := by decide +kernel
theorem fusedMap0616swap_checked : acceptsGraphIso
    (fused (graph core0616) (root 7) 1 0) DegreeOneSmallSpectrum199.graph fusedMap0616swap=true := by decide +kernel
theorem certified0616swap : Certified (graph core0616) (root 7) 1 0 :=
  of_native_maps core0616 DegreeOneSmallSpectrum328.graph DegreeOneSmallSpectrum199.graph
    sourceMap0616swap fusedMap0616swap sourceMap0616swap_checked fusedMap0616swap_checked
    DegreeOneSmallComparisons.comparison0616
#print axioms sourceMap0616swap_checked
#print axioms fusedMap0616swap_checked
#print axioms certified0616swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
