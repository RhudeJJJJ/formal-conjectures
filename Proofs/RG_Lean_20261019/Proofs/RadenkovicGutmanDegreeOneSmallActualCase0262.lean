/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0262 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0262 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 1 2 v)
def fusedMap0262 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0262_checked : acceptsGraphIso
    (source (graph core0262) (root 5) 1 2) DegreeOneSmallSpectrum235.graph sourceMap0262=true := by decide +kernel
theorem fusedMap0262_checked : acceptsGraphIso
    (fused (graph core0262) (root 5) 1 2) SmallGeFourSpectrum037.graph fusedMap0262=true := by decide +kernel
theorem certified0262 : Certified (graph core0262) (root 5) 1 2 :=
  of_native_maps core0262 DegreeOneSmallSpectrum235.graph SmallGeFourSpectrum037.graph
    sourceMap0262 fusedMap0262 sourceMap0262_checked fusedMap0262_checked
    DegreeOneSmallComparisons.comparison0262
#print axioms sourceMap0262_checked
#print axioms fusedMap0262_checked
#print axioms certified0262
def sourceMap0262swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,8,9,10,6,7] (sourceLabel 5 2 1 v)
def fusedMap0262swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0262swap_checked : acceptsGraphIso
    (source (graph core0262) (root 5) 2 1) DegreeOneSmallSpectrum235.graph sourceMap0262swap=true := by decide +kernel
theorem fusedMap0262swap_checked : acceptsGraphIso
    (fused (graph core0262) (root 5) 2 1) SmallGeFourSpectrum037.graph fusedMap0262swap=true := by decide +kernel
theorem certified0262swap : Certified (graph core0262) (root 5) 2 1 :=
  of_native_maps core0262 DegreeOneSmallSpectrum235.graph SmallGeFourSpectrum037.graph
    sourceMap0262swap fusedMap0262swap sourceMap0262swap_checked fusedMap0262swap_checked
    DegreeOneSmallComparisons.comparison0262
#print axioms sourceMap0262swap_checked
#print axioms fusedMap0262swap_checked
#print axioms certified0262swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
