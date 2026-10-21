/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0050 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0050 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,6,7,3,4,5,1,0,8,9,10,11,12] (sourceLabel 2 2 6 v)
def fusedMap0050 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 2 6 v)
theorem sourceMap0050_checked : acceptsGraphIso
    (source (graph core0050) (root 2) 2 6) DegreeOneSmallSpectrum951.graph sourceMap0050=true := by decide +kernel
theorem fusedMap0050_checked : acceptsGraphIso
    (fused (graph core0050) (root 2) 2 6) DegreeOneSmallSpectrum861.graph fusedMap0050=true := by decide +kernel
theorem certified0050 : Certified (graph core0050) (root 2) 2 6 :=
  of_native_maps core0050 DegreeOneSmallSpectrum951.graph DegreeOneSmallSpectrum861.graph
    sourceMap0050 fusedMap0050 sourceMap0050_checked fusedMap0050_checked
    DegreeOneSmallComparisons.comparison0050
#print axioms sourceMap0050_checked
#print axioms fusedMap0050_checked
#print axioms certified0050
def sourceMap0050swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,6,7,1,0,8,9,10,11,12,3,4,5] (sourceLabel 2 6 2 v)
def fusedMap0050swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 6 2 v)
theorem sourceMap0050swap_checked : acceptsGraphIso
    (source (graph core0050) (root 2) 6 2) DegreeOneSmallSpectrum951.graph sourceMap0050swap=true := by decide +kernel
theorem fusedMap0050swap_checked : acceptsGraphIso
    (fused (graph core0050) (root 2) 6 2) DegreeOneSmallSpectrum861.graph fusedMap0050swap=true := by decide +kernel
theorem certified0050swap : Certified (graph core0050) (root 2) 6 2 :=
  of_native_maps core0050 DegreeOneSmallSpectrum951.graph DegreeOneSmallSpectrum861.graph
    sourceMap0050swap fusedMap0050swap sourceMap0050swap_checked fusedMap0050swap_checked
    DegreeOneSmallComparisons.comparison0050
#print axioms sourceMap0050swap_checked
#print axioms fusedMap0050swap_checked
#print axioms certified0050swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
