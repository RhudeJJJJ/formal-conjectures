/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0752 : Family 8 := level8.get ⟨4,by decide⟩
def sourceMap0752 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0752 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0752_checked : acceptsGraphIso
    (source (graph core0752) (root 8) 0 1) DegreeOneSmallSpectrum385.graph sourceMap0752=true := by decide +kernel
theorem fusedMap0752_checked : acceptsGraphIso
    (fused (graph core0752) (root 8) 0 1) DegreeOneSmallSpectrum396.graph fusedMap0752=true := by decide +kernel
theorem certified0752 : Certified (graph core0752) (root 8) 0 1 :=
  of_native_maps core0752 DegreeOneSmallSpectrum385.graph DegreeOneSmallSpectrum396.graph
    sourceMap0752 fusedMap0752 sourceMap0752_checked fusedMap0752_checked
    DegreeOneSmallComparisons.comparison0752
#print axioms sourceMap0752_checked
#print axioms fusedMap0752_checked
#print axioms certified0752
def sourceMap0752swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0752swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0752swap_checked : acceptsGraphIso
    (source (graph core0752) (root 8) 1 0) DegreeOneSmallSpectrum385.graph sourceMap0752swap=true := by decide +kernel
theorem fusedMap0752swap_checked : acceptsGraphIso
    (fused (graph core0752) (root 8) 1 0) DegreeOneSmallSpectrum396.graph fusedMap0752swap=true := by decide +kernel
theorem certified0752swap : Certified (graph core0752) (root 8) 1 0 :=
  of_native_maps core0752 DegreeOneSmallSpectrum385.graph DegreeOneSmallSpectrum396.graph
    sourceMap0752swap fusedMap0752swap sourceMap0752swap_checked fusedMap0752swap_checked
    DegreeOneSmallComparisons.comparison0752
#print axioms sourceMap0752swap_checked
#print axioms fusedMap0752swap_checked
#print axioms certified0752swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
