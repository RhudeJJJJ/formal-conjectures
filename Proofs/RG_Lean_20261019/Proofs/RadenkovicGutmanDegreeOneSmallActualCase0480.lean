/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0480 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0480 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 7 0 3 v)
def fusedMap0480 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0480_checked : acceptsGraphIso
    (source (graph core0480) (root 7) 0 3) DegreeOneSmallSpectrum976.graph sourceMap0480=true := by decide +kernel
theorem fusedMap0480_checked : acceptsGraphIso
    (fused (graph core0480) (root 7) 0 3) DegreeOneSmallSpectrum860.graph fusedMap0480=true := by decide +kernel
theorem certified0480 : Certified (graph core0480) (root 7) 0 3 :=
  of_native_maps core0480 DegreeOneSmallSpectrum976.graph DegreeOneSmallSpectrum860.graph
    sourceMap0480 fusedMap0480 sourceMap0480_checked fusedMap0480_checked
    DegreeOneSmallComparisons.comparison0480
#print axioms sourceMap0480_checked
#print axioms fusedMap0480_checked
#print axioms certified0480
def sourceMap0480swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 3 0 v)
def fusedMap0480swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0480swap_checked : acceptsGraphIso
    (source (graph core0480) (root 7) 3 0) DegreeOneSmallSpectrum976.graph sourceMap0480swap=true := by decide +kernel
theorem fusedMap0480swap_checked : acceptsGraphIso
    (fused (graph core0480) (root 7) 3 0) DegreeOneSmallSpectrum860.graph fusedMap0480swap=true := by decide +kernel
theorem certified0480swap : Certified (graph core0480) (root 7) 3 0 :=
  of_native_maps core0480 DegreeOneSmallSpectrum976.graph DegreeOneSmallSpectrum860.graph
    sourceMap0480swap fusedMap0480swap sourceMap0480swap_checked fusedMap0480swap_checked
    DegreeOneSmallComparisons.comparison0480
#print axioms sourceMap0480swap_checked
#print axioms fusedMap0480swap_checked
#print axioms certified0480swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
