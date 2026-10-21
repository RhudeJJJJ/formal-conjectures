/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0725 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0725 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0725 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0725_checked : acceptsGraphIso
    (source (graph core0725) (root 7) 0 2) SmallGeFourSpectrum183.graph sourceMap0725=true := by decide +kernel
theorem fusedMap0725_checked : acceptsGraphIso
    (fused (graph core0725) (root 7) 0 2) SmallGeFourSpectrum100.graph fusedMap0725=true := by decide +kernel
theorem certified0725 : Certified (graph core0725) (root 7) 0 2 :=
  of_native_maps core0725 SmallGeFourSpectrum183.graph SmallGeFourSpectrum100.graph
    sourceMap0725 fusedMap0725 sourceMap0725_checked fusedMap0725_checked
    DegreeOneSmallComparisons.comparison0725
#print axioms sourceMap0725_checked
#print axioms fusedMap0725_checked
#print axioms certified0725
def sourceMap0725swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0725swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0725swap_checked : acceptsGraphIso
    (source (graph core0725) (root 7) 2 0) SmallGeFourSpectrum183.graph sourceMap0725swap=true := by decide +kernel
theorem fusedMap0725swap_checked : acceptsGraphIso
    (fused (graph core0725) (root 7) 2 0) SmallGeFourSpectrum100.graph fusedMap0725swap=true := by decide +kernel
theorem certified0725swap : Certified (graph core0725) (root 7) 2 0 :=
  of_native_maps core0725 SmallGeFourSpectrum183.graph SmallGeFourSpectrum100.graph
    sourceMap0725swap fusedMap0725swap sourceMap0725swap_checked fusedMap0725swap_checked
    DegreeOneSmallComparisons.comparison0725
#print axioms sourceMap0725swap_checked
#print axioms fusedMap0725swap_checked
#print axioms certified0725swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
