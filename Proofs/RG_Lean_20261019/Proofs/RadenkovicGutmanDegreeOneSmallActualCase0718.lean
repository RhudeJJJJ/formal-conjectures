/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0718 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0718 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0718 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0718_checked : acceptsGraphIso
    (source (graph core0718) (root 7) 0 1) SmallGeFourSpectrum057.graph sourceMap0718=true := by decide +kernel
theorem fusedMap0718_checked : acceptsGraphIso
    (fused (graph core0718) (root 7) 0 1) SmallGeFourSpectrum058.graph fusedMap0718=true := by decide +kernel
theorem certified0718 : Certified (graph core0718) (root 7) 0 1 :=
  of_native_maps core0718 SmallGeFourSpectrum057.graph SmallGeFourSpectrum058.graph
    sourceMap0718 fusedMap0718 sourceMap0718_checked fusedMap0718_checked
    DegreeOneSmallComparisons.comparison0718
#print axioms sourceMap0718_checked
#print axioms fusedMap0718_checked
#print axioms certified0718
def sourceMap0718swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0718swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0718swap_checked : acceptsGraphIso
    (source (graph core0718) (root 7) 1 0) SmallGeFourSpectrum057.graph sourceMap0718swap=true := by decide +kernel
theorem fusedMap0718swap_checked : acceptsGraphIso
    (fused (graph core0718) (root 7) 1 0) SmallGeFourSpectrum058.graph fusedMap0718swap=true := by decide +kernel
theorem certified0718swap : Certified (graph core0718) (root 7) 1 0 :=
  of_native_maps core0718 SmallGeFourSpectrum057.graph SmallGeFourSpectrum058.graph
    sourceMap0718swap fusedMap0718swap sourceMap0718swap_checked fusedMap0718swap_checked
    DegreeOneSmallComparisons.comparison0718
#print axioms sourceMap0718swap_checked
#print axioms fusedMap0718swap_checked
#print axioms certified0718swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
