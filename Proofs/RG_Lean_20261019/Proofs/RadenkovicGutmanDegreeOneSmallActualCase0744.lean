/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0744 : Family 8 := level8.get ⟨2,by decide⟩
def sourceMap0744 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0744 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0744_checked : acceptsGraphIso
    (source (graph core0744) (root 8) 0 1) DegreeOneSmallSpectrum383.graph sourceMap0744=true := by decide +kernel
theorem fusedMap0744_checked : acceptsGraphIso
    (fused (graph core0744) (root 8) 0 1) DegreeOneSmallSpectrum386.graph fusedMap0744=true := by decide +kernel
theorem certified0744 : Certified (graph core0744) (root 8) 0 1 :=
  of_native_maps core0744 DegreeOneSmallSpectrum383.graph DegreeOneSmallSpectrum386.graph
    sourceMap0744 fusedMap0744 sourceMap0744_checked fusedMap0744_checked
    DegreeOneSmallComparisons.comparison0744
#print axioms sourceMap0744_checked
#print axioms fusedMap0744_checked
#print axioms certified0744
def sourceMap0744swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0744swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0744swap_checked : acceptsGraphIso
    (source (graph core0744) (root 8) 1 0) DegreeOneSmallSpectrum383.graph sourceMap0744swap=true := by decide +kernel
theorem fusedMap0744swap_checked : acceptsGraphIso
    (fused (graph core0744) (root 8) 1 0) DegreeOneSmallSpectrum386.graph fusedMap0744swap=true := by decide +kernel
theorem certified0744swap : Certified (graph core0744) (root 8) 1 0 :=
  of_native_maps core0744 DegreeOneSmallSpectrum383.graph DegreeOneSmallSpectrum386.graph
    sourceMap0744swap fusedMap0744swap sourceMap0744swap_checked fusedMap0744swap_checked
    DegreeOneSmallComparisons.comparison0744
#print axioms sourceMap0744swap_checked
#print axioms fusedMap0744swap_checked
#print axioms certified0744swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
