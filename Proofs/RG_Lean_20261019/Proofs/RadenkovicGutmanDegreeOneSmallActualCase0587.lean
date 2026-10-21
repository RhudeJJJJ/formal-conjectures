/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0587 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0587 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0587 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0587_checked : acceptsGraphIso
    (source (graph core0587) (root 7) 0 2) DegreeOneSmallSpectrum439.graph sourceMap0587=true := by decide +kernel
theorem fusedMap0587_checked : acceptsGraphIso
    (fused (graph core0587) (root 7) 0 2) DegreeOneSmallSpectrum440.graph fusedMap0587=true := by decide +kernel
theorem certified0587 : Certified (graph core0587) (root 7) 0 2 :=
  of_native_maps core0587 DegreeOneSmallSpectrum439.graph DegreeOneSmallSpectrum440.graph
    sourceMap0587 fusedMap0587 sourceMap0587_checked fusedMap0587_checked
    DegreeOneSmallComparisons.comparison0587
#print axioms sourceMap0587_checked
#print axioms fusedMap0587_checked
#print axioms certified0587
def sourceMap0587swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0587swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0587swap_checked : acceptsGraphIso
    (source (graph core0587) (root 7) 2 0) DegreeOneSmallSpectrum439.graph sourceMap0587swap=true := by decide +kernel
theorem fusedMap0587swap_checked : acceptsGraphIso
    (fused (graph core0587) (root 7) 2 0) DegreeOneSmallSpectrum440.graph fusedMap0587swap=true := by decide +kernel
theorem certified0587swap : Certified (graph core0587) (root 7) 2 0 :=
  of_native_maps core0587 DegreeOneSmallSpectrum439.graph DegreeOneSmallSpectrum440.graph
    sourceMap0587swap fusedMap0587swap sourceMap0587swap_checked fusedMap0587swap_checked
    DegreeOneSmallComparisons.comparison0587
#print axioms sourceMap0587swap_checked
#print axioms fusedMap0587swap_checked
#print axioms certified0587swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
