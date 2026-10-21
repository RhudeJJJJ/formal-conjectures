/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0599 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0599 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0599 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0599_checked : acceptsGraphIso
    (source (graph core0599) (root 7) 0 2) DegreeOneSmallSpectrum463.graph sourceMap0599=true := by decide +kernel
theorem fusedMap0599_checked : acceptsGraphIso
    (fused (graph core0599) (root 7) 0 2) DegreeOneSmallSpectrum464.graph fusedMap0599=true := by decide +kernel
theorem certified0599 : Certified (graph core0599) (root 7) 0 2 :=
  of_native_maps core0599 DegreeOneSmallSpectrum463.graph DegreeOneSmallSpectrum464.graph
    sourceMap0599 fusedMap0599 sourceMap0599_checked fusedMap0599_checked
    DegreeOneSmallComparisons.comparison0599
#print axioms sourceMap0599_checked
#print axioms fusedMap0599_checked
#print axioms certified0599
def sourceMap0599swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0599swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0599swap_checked : acceptsGraphIso
    (source (graph core0599) (root 7) 2 0) DegreeOneSmallSpectrum463.graph sourceMap0599swap=true := by decide +kernel
theorem fusedMap0599swap_checked : acceptsGraphIso
    (fused (graph core0599) (root 7) 2 0) DegreeOneSmallSpectrum464.graph fusedMap0599swap=true := by decide +kernel
theorem certified0599swap : Certified (graph core0599) (root 7) 2 0 :=
  of_native_maps core0599 DegreeOneSmallSpectrum463.graph DegreeOneSmallSpectrum464.graph
    sourceMap0599swap fusedMap0599swap sourceMap0599swap_checked fusedMap0599swap_checked
    DegreeOneSmallComparisons.comparison0599
#print axioms sourceMap0599swap_checked
#print axioms fusedMap0599swap_checked
#print axioms certified0599swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
