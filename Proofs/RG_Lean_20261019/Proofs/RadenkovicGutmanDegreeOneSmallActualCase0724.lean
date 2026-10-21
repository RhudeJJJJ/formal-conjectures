/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0724 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0724 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0724 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0724_checked : acceptsGraphIso
    (source (graph core0724) (root 7) 0 1) SmallGeFourSpectrum061.graph sourceMap0724=true := by decide +kernel
theorem fusedMap0724_checked : acceptsGraphIso
    (fused (graph core0724) (root 7) 0 1) SmallGeFourSpectrum062.graph fusedMap0724=true := by decide +kernel
theorem certified0724 : Certified (graph core0724) (root 7) 0 1 :=
  of_native_maps core0724 SmallGeFourSpectrum061.graph SmallGeFourSpectrum062.graph
    sourceMap0724 fusedMap0724 sourceMap0724_checked fusedMap0724_checked
    DegreeOneSmallComparisons.comparison0724
#print axioms sourceMap0724_checked
#print axioms fusedMap0724_checked
#print axioms certified0724
def sourceMap0724swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0724swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0724swap_checked : acceptsGraphIso
    (source (graph core0724) (root 7) 1 0) SmallGeFourSpectrum061.graph sourceMap0724swap=true := by decide +kernel
theorem fusedMap0724swap_checked : acceptsGraphIso
    (fused (graph core0724) (root 7) 1 0) SmallGeFourSpectrum062.graph fusedMap0724swap=true := by decide +kernel
theorem certified0724swap : Certified (graph core0724) (root 7) 1 0 :=
  of_native_maps core0724 SmallGeFourSpectrum061.graph SmallGeFourSpectrum062.graph
    sourceMap0724swap fusedMap0724swap sourceMap0724swap_checked fusedMap0724swap_checked
    DegreeOneSmallComparisons.comparison0724
#print axioms sourceMap0724swap_checked
#print axioms fusedMap0724swap_checked
#print axioms certified0724swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
