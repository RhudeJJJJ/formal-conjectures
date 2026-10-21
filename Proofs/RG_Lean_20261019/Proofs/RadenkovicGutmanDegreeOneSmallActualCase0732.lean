/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0732 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0732 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0732 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0732_checked : acceptsGraphIso
    (source (graph core0732) (root 7) 0 3) DegreeOneSmallSpectrum1526.graph sourceMap0732=true := by decide +kernel
theorem fusedMap0732_checked : acceptsGraphIso
    (fused (graph core0732) (root 7) 0 3) DegreeOneSmallSpectrum979.graph fusedMap0732=true := by decide +kernel
theorem certified0732 : Certified (graph core0732) (root 7) 0 3 :=
  of_native_maps core0732 DegreeOneSmallSpectrum1526.graph DegreeOneSmallSpectrum979.graph
    sourceMap0732 fusedMap0732 sourceMap0732_checked fusedMap0732_checked
    DegreeOneSmallComparisons.comparison0732
#print axioms sourceMap0732_checked
#print axioms fusedMap0732_checked
#print axioms certified0732
def sourceMap0732swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,9] (sourceLabel 7 3 0 v)
def fusedMap0732swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0732swap_checked : acceptsGraphIso
    (source (graph core0732) (root 7) 3 0) DegreeOneSmallSpectrum1526.graph sourceMap0732swap=true := by decide +kernel
theorem fusedMap0732swap_checked : acceptsGraphIso
    (fused (graph core0732) (root 7) 3 0) DegreeOneSmallSpectrum979.graph fusedMap0732swap=true := by decide +kernel
theorem certified0732swap : Certified (graph core0732) (root 7) 3 0 :=
  of_native_maps core0732 DegreeOneSmallSpectrum1526.graph DegreeOneSmallSpectrum979.graph
    sourceMap0732swap fusedMap0732swap sourceMap0732swap_checked fusedMap0732swap_checked
    DegreeOneSmallComparisons.comparison0732
#print axioms sourceMap0732swap_checked
#print axioms fusedMap0732swap_checked
#print axioms certified0732swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
