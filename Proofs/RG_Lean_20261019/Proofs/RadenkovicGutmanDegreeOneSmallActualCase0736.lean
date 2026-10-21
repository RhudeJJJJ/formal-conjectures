/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0736 : Family 8 := level8.get ⟨0,by decide⟩
def sourceMap0736 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 8 0 1 v)
def fusedMap0736 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (fusedLabel 8 0 1 v)
theorem sourceMap0736_checked : acceptsGraphIso
    (source (graph core0736) (root 8) 0 1) DegreeOneSmallSpectrum386.graph sourceMap0736=true := by decide +kernel
theorem fusedMap0736_checked : acceptsGraphIso
    (fused (graph core0736) (root 8) 0 1) DegreeOneSmallSpectrum369.graph fusedMap0736=true := by decide +kernel
theorem certified0736 : Certified (graph core0736) (root 8) 0 1 :=
  of_native_maps core0736 DegreeOneSmallSpectrum386.graph DegreeOneSmallSpectrum369.graph
    sourceMap0736 fusedMap0736 sourceMap0736_checked fusedMap0736_checked
    DegreeOneSmallComparisons.comparison0736
#print axioms sourceMap0736_checked
#print axioms fusedMap0736_checked
#print axioms certified0736
def sourceMap0736swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,4,5,6] (sourceLabel 8 1 0 v)
def fusedMap0736swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (fusedLabel 8 1 0 v)
theorem sourceMap0736swap_checked : acceptsGraphIso
    (source (graph core0736) (root 8) 1 0) DegreeOneSmallSpectrum386.graph sourceMap0736swap=true := by decide +kernel
theorem fusedMap0736swap_checked : acceptsGraphIso
    (fused (graph core0736) (root 8) 1 0) DegreeOneSmallSpectrum369.graph fusedMap0736swap=true := by decide +kernel
theorem certified0736swap : Certified (graph core0736) (root 8) 1 0 :=
  of_native_maps core0736 DegreeOneSmallSpectrum386.graph DegreeOneSmallSpectrum369.graph
    sourceMap0736swap fusedMap0736swap sourceMap0736swap_checked fusedMap0736swap_checked
    DegreeOneSmallComparisons.comparison0736
#print axioms sourceMap0736swap_checked
#print axioms fusedMap0736swap_checked
#print axioms certified0736swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
