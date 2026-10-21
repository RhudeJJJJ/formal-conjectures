/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0868 : Family 8 := level8.get ⟨42,by decide⟩
def sourceMap0868 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap0868 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0868_checked : acceptsGraphIso
    (source (graph core0868) (root 8) 0 1) DegreeOneSmallSpectrum452.graph sourceMap0868=true := by decide +kernel
theorem fusedMap0868_checked : acceptsGraphIso
    (fused (graph core0868) (root 8) 0 1) DegreeOneSmallSpectrum457.graph fusedMap0868=true := by decide +kernel
theorem certified0868 : Certified (graph core0868) (root 8) 0 1 :=
  of_native_maps core0868 DegreeOneSmallSpectrum452.graph DegreeOneSmallSpectrum457.graph
    sourceMap0868 fusedMap0868 sourceMap0868_checked fusedMap0868_checked
    DegreeOneSmallComparisons.comparison0868
#print axioms sourceMap0868_checked
#print axioms fusedMap0868_checked
#print axioms certified0868
def sourceMap0868swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap0868swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0868swap_checked : acceptsGraphIso
    (source (graph core0868) (root 8) 1 0) DegreeOneSmallSpectrum452.graph sourceMap0868swap=true := by decide +kernel
theorem fusedMap0868swap_checked : acceptsGraphIso
    (fused (graph core0868) (root 8) 1 0) DegreeOneSmallSpectrum457.graph fusedMap0868swap=true := by decide +kernel
theorem certified0868swap : Certified (graph core0868) (root 8) 1 0 :=
  of_native_maps core0868 DegreeOneSmallSpectrum452.graph DegreeOneSmallSpectrum457.graph
    sourceMap0868swap fusedMap0868swap sourceMap0868swap_checked fusedMap0868swap_checked
    DegreeOneSmallComparisons.comparison0868
#print axioms sourceMap0868swap_checked
#print axioms fusedMap0868swap_checked
#print axioms certified0868swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
