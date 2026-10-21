/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0845 : Family 8 := level8.get ⟨35,by decide⟩
def sourceMap0845 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0845 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0845_checked : acceptsGraphIso
    (source (graph core0845) (root 8) 0 2) DegreeOneSmallSpectrum1036.graph sourceMap0845=true := by decide +kernel
theorem fusedMap0845_checked : acceptsGraphIso
    (fused (graph core0845) (root 8) 0 2) DegreeOneSmallSpectrum863.graph fusedMap0845=true := by decide +kernel
theorem certified0845 : Certified (graph core0845) (root 8) 0 2 :=
  of_native_maps core0845 DegreeOneSmallSpectrum1036.graph DegreeOneSmallSpectrum863.graph
    sourceMap0845 fusedMap0845 sourceMap0845_checked fusedMap0845_checked
    DegreeOneSmallComparisons.comparison0845
#print axioms sourceMap0845_checked
#print axioms fusedMap0845_checked
#print axioms certified0845
def sourceMap0845swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0845swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0845swap_checked : acceptsGraphIso
    (source (graph core0845) (root 8) 2 0) DegreeOneSmallSpectrum1036.graph sourceMap0845swap=true := by decide +kernel
theorem fusedMap0845swap_checked : acceptsGraphIso
    (fused (graph core0845) (root 8) 2 0) DegreeOneSmallSpectrum863.graph fusedMap0845swap=true := by decide +kernel
theorem certified0845swap : Certified (graph core0845) (root 8) 2 0 :=
  of_native_maps core0845 DegreeOneSmallSpectrum1036.graph DegreeOneSmallSpectrum863.graph
    sourceMap0845swap fusedMap0845swap sourceMap0845swap_checked fusedMap0845swap_checked
    DegreeOneSmallComparisons.comparison0845
#print axioms sourceMap0845swap_checked
#print axioms fusedMap0845swap_checked
#print axioms certified0845swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
