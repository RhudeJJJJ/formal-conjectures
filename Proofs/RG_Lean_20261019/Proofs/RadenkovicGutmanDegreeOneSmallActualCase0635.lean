/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0635 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0635 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0635 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0635_checked : acceptsGraphIso
    (source (graph core0635) (root 7) 0 2) DegreeOneSmallSpectrum539.graph sourceMap0635=true := by decide +kernel
theorem fusedMap0635_checked : acceptsGraphIso
    (fused (graph core0635) (root 7) 0 2) DegreeOneSmallSpectrum540.graph fusedMap0635=true := by decide +kernel
theorem certified0635 : Certified (graph core0635) (root 7) 0 2 :=
  of_native_maps core0635 DegreeOneSmallSpectrum539.graph DegreeOneSmallSpectrum540.graph
    sourceMap0635 fusedMap0635 sourceMap0635_checked fusedMap0635_checked
    DegreeOneSmallComparisons.comparison0635
#print axioms sourceMap0635_checked
#print axioms fusedMap0635_checked
#print axioms certified0635
def sourceMap0635swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0635swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0635swap_checked : acceptsGraphIso
    (source (graph core0635) (root 7) 2 0) DegreeOneSmallSpectrum539.graph sourceMap0635swap=true := by decide +kernel
theorem fusedMap0635swap_checked : acceptsGraphIso
    (fused (graph core0635) (root 7) 2 0) DegreeOneSmallSpectrum540.graph fusedMap0635swap=true := by decide +kernel
theorem certified0635swap : Certified (graph core0635) (root 7) 2 0 :=
  of_native_maps core0635 DegreeOneSmallSpectrum539.graph DegreeOneSmallSpectrum540.graph
    sourceMap0635swap fusedMap0635swap sourceMap0635swap_checked fusedMap0635swap_checked
    DegreeOneSmallComparisons.comparison0635
#print axioms sourceMap0635swap_checked
#print axioms fusedMap0635swap_checked
#print axioms certified0635swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
