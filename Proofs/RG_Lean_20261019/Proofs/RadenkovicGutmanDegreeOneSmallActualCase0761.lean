/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0761 : Family 8 := level8.get ⟨6,by decide⟩
def sourceMap0761 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,3,4,5] (sourceLabel 8 0 2 v)
def fusedMap0761 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 0 2 v)
theorem sourceMap0761_checked : acceptsGraphIso
    (source (graph core0761) (root 8) 0 2) DegreeOneSmallSpectrum961.graph sourceMap0761=true := by decide +kernel
theorem fusedMap0761_checked : acceptsGraphIso
    (fused (graph core0761) (root 8) 0 2) DegreeOneSmallSpectrum860.graph fusedMap0761=true := by decide +kernel
theorem certified0761 : Certified (graph core0761) (root 8) 0 2 :=
  of_native_maps core0761 DegreeOneSmallSpectrum961.graph DegreeOneSmallSpectrum860.graph
    sourceMap0761 fusedMap0761 sourceMap0761_checked fusedMap0761_checked
    DegreeOneSmallComparisons.comparison0761
#print axioms sourceMap0761_checked
#print axioms fusedMap0761_checked
#print axioms certified0761
def sourceMap0761swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 8 2 0 v)
def fusedMap0761swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 8 2 0 v)
theorem sourceMap0761swap_checked : acceptsGraphIso
    (source (graph core0761) (root 8) 2 0) DegreeOneSmallSpectrum961.graph sourceMap0761swap=true := by decide +kernel
theorem fusedMap0761swap_checked : acceptsGraphIso
    (fused (graph core0761) (root 8) 2 0) DegreeOneSmallSpectrum860.graph fusedMap0761swap=true := by decide +kernel
theorem certified0761swap : Certified (graph core0761) (root 8) 2 0 :=
  of_native_maps core0761 DegreeOneSmallSpectrum961.graph DegreeOneSmallSpectrum860.graph
    sourceMap0761swap fusedMap0761swap sourceMap0761swap_checked fusedMap0761swap_checked
    DegreeOneSmallComparisons.comparison0761
#print axioms sourceMap0761swap_checked
#print axioms fusedMap0761swap_checked
#print axioms certified0761swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
