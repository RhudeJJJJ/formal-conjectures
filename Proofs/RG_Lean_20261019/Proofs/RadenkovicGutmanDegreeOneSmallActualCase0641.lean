/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0641 : Family 7 := level7.get ⟨46,by decide⟩
def sourceMap0641 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0641 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0641_checked : acceptsGraphIso
    (source (graph core0641) (root 7) 0 2) DegreeOneSmallSpectrum543.graph sourceMap0641=true := by decide +kernel
theorem fusedMap0641_checked : acceptsGraphIso
    (fused (graph core0641) (root 7) 0 2) DegreeOneSmallSpectrum544.graph fusedMap0641=true := by decide +kernel
theorem certified0641 : Certified (graph core0641) (root 7) 0 2 :=
  of_native_maps core0641 DegreeOneSmallSpectrum543.graph DegreeOneSmallSpectrum544.graph
    sourceMap0641 fusedMap0641 sourceMap0641_checked fusedMap0641_checked
    DegreeOneSmallComparisons.comparison0641
#print axioms sourceMap0641_checked
#print axioms fusedMap0641_checked
#print axioms certified0641
def sourceMap0641swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0641swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0641swap_checked : acceptsGraphIso
    (source (graph core0641) (root 7) 2 0) DegreeOneSmallSpectrum543.graph sourceMap0641swap=true := by decide +kernel
theorem fusedMap0641swap_checked : acceptsGraphIso
    (fused (graph core0641) (root 7) 2 0) DegreeOneSmallSpectrum544.graph fusedMap0641swap=true := by decide +kernel
theorem certified0641swap : Certified (graph core0641) (root 7) 2 0 :=
  of_native_maps core0641 DegreeOneSmallSpectrum543.graph DegreeOneSmallSpectrum544.graph
    sourceMap0641swap fusedMap0641swap sourceMap0641swap_checked fusedMap0641swap_checked
    DegreeOneSmallComparisons.comparison0641
#print axioms sourceMap0641swap_checked
#print axioms fusedMap0641swap_checked
#print axioms certified0641swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
