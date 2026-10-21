/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0509 : Family 7 := level7.get ⟨12,by decide⟩
def sourceMap0509 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0509 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0509_checked : acceptsGraphIso
    (source (graph core0509) (root 7) 0 2) DegreeOneSmallSpectrum517.graph sourceMap0509=true := by decide +kernel
theorem fusedMap0509_checked : acceptsGraphIso
    (fused (graph core0509) (root 7) 0 2) DegreeOneSmallSpectrum379.graph fusedMap0509=true := by decide +kernel
theorem certified0509 : Certified (graph core0509) (root 7) 0 2 :=
  of_native_maps core0509 DegreeOneSmallSpectrum517.graph DegreeOneSmallSpectrum379.graph
    sourceMap0509 fusedMap0509 sourceMap0509_checked fusedMap0509_checked
    DegreeOneSmallComparisons.comparison0509
#print axioms sourceMap0509_checked
#print axioms fusedMap0509_checked
#print axioms certified0509
def sourceMap0509swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0509swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0509swap_checked : acceptsGraphIso
    (source (graph core0509) (root 7) 2 0) DegreeOneSmallSpectrum517.graph sourceMap0509swap=true := by decide +kernel
theorem fusedMap0509swap_checked : acceptsGraphIso
    (fused (graph core0509) (root 7) 2 0) DegreeOneSmallSpectrum379.graph fusedMap0509swap=true := by decide +kernel
theorem certified0509swap : Certified (graph core0509) (root 7) 2 0 :=
  of_native_maps core0509 DegreeOneSmallSpectrum517.graph DegreeOneSmallSpectrum379.graph
    sourceMap0509swap fusedMap0509swap sourceMap0509swap_checked fusedMap0509swap_checked
    DegreeOneSmallComparisons.comparison0509
#print axioms sourceMap0509swap_checked
#print axioms fusedMap0509swap_checked
#print axioms certified0509swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
