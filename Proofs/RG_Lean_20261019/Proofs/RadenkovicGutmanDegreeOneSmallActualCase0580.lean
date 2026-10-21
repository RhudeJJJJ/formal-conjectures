/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0580 : Family 7 := level7.get ⟨30,by decide⟩
def sourceMap0580 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0580 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0580_checked : acceptsGraphIso
    (source (graph core0580) (root 7) 0 1) DegreeOneSmallSpectrum280.graph sourceMap0580=true := by decide +kernel
theorem fusedMap0580_checked : acceptsGraphIso
    (fused (graph core0580) (root 7) 0 1) DegreeOneSmallSpectrum176.graph fusedMap0580=true := by decide +kernel
theorem certified0580 : Certified (graph core0580) (root 7) 0 1 :=
  of_native_maps core0580 DegreeOneSmallSpectrum280.graph DegreeOneSmallSpectrum176.graph
    sourceMap0580 fusedMap0580 sourceMap0580_checked fusedMap0580_checked
    DegreeOneSmallComparisons.comparison0580
#print axioms sourceMap0580_checked
#print axioms fusedMap0580_checked
#print axioms certified0580
def sourceMap0580swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0580swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0580swap_checked : acceptsGraphIso
    (source (graph core0580) (root 7) 1 0) DegreeOneSmallSpectrum280.graph sourceMap0580swap=true := by decide +kernel
theorem fusedMap0580swap_checked : acceptsGraphIso
    (fused (graph core0580) (root 7) 1 0) DegreeOneSmallSpectrum176.graph fusedMap0580swap=true := by decide +kernel
theorem certified0580swap : Certified (graph core0580) (root 7) 1 0 :=
  of_native_maps core0580 DegreeOneSmallSpectrum280.graph DegreeOneSmallSpectrum176.graph
    sourceMap0580swap fusedMap0580swap sourceMap0580swap_checked fusedMap0580swap_checked
    DegreeOneSmallComparisons.comparison0580
#print axioms sourceMap0580swap_checked
#print axioms fusedMap0580swap_checked
#print axioms certified0580swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
