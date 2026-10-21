/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0540 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0540 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0540 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0540_checked : acceptsGraphIso
    (source (graph core0540) (root 7) 0 3) DegreeOneSmallSpectrum955.graph sourceMap0540=true := by decide +kernel
theorem fusedMap0540_checked : acceptsGraphIso
    (fused (graph core0540) (root 7) 0 3) DegreeOneSmallSpectrum956.graph fusedMap0540=true := by decide +kernel
theorem certified0540 : Certified (graph core0540) (root 7) 0 3 :=
  of_native_maps core0540 DegreeOneSmallSpectrum955.graph DegreeOneSmallSpectrum956.graph
    sourceMap0540 fusedMap0540 sourceMap0540_checked fusedMap0540_checked
    DegreeOneSmallComparisons.comparison0540
#print axioms sourceMap0540_checked
#print axioms fusedMap0540_checked
#print axioms certified0540
def sourceMap0540swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0540swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0540swap_checked : acceptsGraphIso
    (source (graph core0540) (root 7) 3 0) DegreeOneSmallSpectrum955.graph sourceMap0540swap=true := by decide +kernel
theorem fusedMap0540swap_checked : acceptsGraphIso
    (fused (graph core0540) (root 7) 3 0) DegreeOneSmallSpectrum956.graph fusedMap0540swap=true := by decide +kernel
theorem certified0540swap : Certified (graph core0540) (root 7) 3 0 :=
  of_native_maps core0540 DegreeOneSmallSpectrum955.graph DegreeOneSmallSpectrum956.graph
    sourceMap0540swap fusedMap0540swap sourceMap0540swap_checked fusedMap0540swap_checked
    DegreeOneSmallComparisons.comparison0540
#print axioms sourceMap0540swap_checked
#print axioms fusedMap0540swap_checked
#print axioms certified0540swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
