/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0805 : Family 8 := level8.get ⟨20,by decide⟩
def sourceMap0805 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0805 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0805_checked : acceptsGraphIso
    (source (graph core0805) (root 8) 0 2) DegreeOneSmallSpectrum949.graph sourceMap0805=true := by decide +kernel
theorem fusedMap0805_checked : acceptsGraphIso
    (fused (graph core0805) (root 8) 0 2) DegreeOneSmallSpectrum951.graph fusedMap0805=true := by decide +kernel
theorem certified0805 : Certified (graph core0805) (root 8) 0 2 :=
  of_native_maps core0805 DegreeOneSmallSpectrum949.graph DegreeOneSmallSpectrum951.graph
    sourceMap0805 fusedMap0805 sourceMap0805_checked fusedMap0805_checked
    DegreeOneSmallComparisons.comparison0805
#print axioms sourceMap0805_checked
#print axioms fusedMap0805_checked
#print axioms certified0805
def sourceMap0805swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0805swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0805swap_checked : acceptsGraphIso
    (source (graph core0805) (root 8) 2 0) DegreeOneSmallSpectrum949.graph sourceMap0805swap=true := by decide +kernel
theorem fusedMap0805swap_checked : acceptsGraphIso
    (fused (graph core0805) (root 8) 2 0) DegreeOneSmallSpectrum951.graph fusedMap0805swap=true := by decide +kernel
theorem certified0805swap : Certified (graph core0805) (root 8) 2 0 :=
  of_native_maps core0805 DegreeOneSmallSpectrum949.graph DegreeOneSmallSpectrum951.graph
    sourceMap0805swap fusedMap0805swap sourceMap0805swap_checked fusedMap0805swap_checked
    DegreeOneSmallComparisons.comparison0805
#print axioms sourceMap0805swap_checked
#print axioms fusedMap0805swap_checked
#print axioms certified0805swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
