/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0592 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0592 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (sourceLabel 7 0 1 v)
def fusedMap0592 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0592_checked : acceptsGraphIso
    (source (graph core0592) (root 7) 0 1) DegreeOneSmallSpectrum298.graph sourceMap0592=true := by decide +kernel
theorem fusedMap0592_checked : acceptsGraphIso
    (fused (graph core0592) (root 7) 0 1) DegreeOneSmallSpectrum178.graph fusedMap0592=true := by decide +kernel
theorem certified0592 : Certified (graph core0592) (root 7) 0 1 :=
  of_native_maps core0592 DegreeOneSmallSpectrum298.graph DegreeOneSmallSpectrum178.graph
    sourceMap0592 fusedMap0592 sourceMap0592_checked fusedMap0592_checked
    DegreeOneSmallComparisons.comparison0592
#print axioms sourceMap0592_checked
#print axioms fusedMap0592_checked
#print axioms certified0592
def sourceMap0592swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 7 1 0 v)
def fusedMap0592swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0592swap_checked : acceptsGraphIso
    (source (graph core0592) (root 7) 1 0) DegreeOneSmallSpectrum298.graph sourceMap0592swap=true := by decide +kernel
theorem fusedMap0592swap_checked : acceptsGraphIso
    (fused (graph core0592) (root 7) 1 0) DegreeOneSmallSpectrum178.graph fusedMap0592swap=true := by decide +kernel
theorem certified0592swap : Certified (graph core0592) (root 7) 1 0 :=
  of_native_maps core0592 DegreeOneSmallSpectrum298.graph DegreeOneSmallSpectrum178.graph
    sourceMap0592swap fusedMap0592swap sourceMap0592swap_checked fusedMap0592swap_checked
    DegreeOneSmallComparisons.comparison0592
#print axioms sourceMap0592swap_checked
#print axioms fusedMap0592swap_checked
#print axioms certified0592swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
