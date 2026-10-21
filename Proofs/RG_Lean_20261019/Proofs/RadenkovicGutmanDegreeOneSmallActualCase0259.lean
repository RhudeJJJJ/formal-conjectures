/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0259 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0259 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0259 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0259_checked : acceptsGraphIso
    (source (graph core0259) (root 5) 0 4) DegreeOneSmallSpectrum399.graph sourceMap0259=true := by decide +kernel
theorem fusedMap0259_checked : acceptsGraphIso
    (fused (graph core0259) (root 5) 0 4) SmallGeFourSpectrum094.graph fusedMap0259=true := by decide +kernel
theorem certified0259 : Certified (graph core0259) (root 5) 0 4 :=
  of_native_maps core0259 DegreeOneSmallSpectrum399.graph SmallGeFourSpectrum094.graph
    sourceMap0259 fusedMap0259 sourceMap0259_checked fusedMap0259_checked
    DegreeOneSmallComparisons.comparison0259
#print axioms sourceMap0259_checked
#print axioms fusedMap0259_checked
#print axioms certified0259
def sourceMap0259swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap0259swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0259swap_checked : acceptsGraphIso
    (source (graph core0259) (root 5) 4 0) DegreeOneSmallSpectrum399.graph sourceMap0259swap=true := by decide +kernel
theorem fusedMap0259swap_checked : acceptsGraphIso
    (fused (graph core0259) (root 5) 4 0) SmallGeFourSpectrum094.graph fusedMap0259swap=true := by decide +kernel
theorem certified0259swap : Certified (graph core0259) (root 5) 4 0 :=
  of_native_maps core0259 DegreeOneSmallSpectrum399.graph SmallGeFourSpectrum094.graph
    sourceMap0259swap fusedMap0259swap sourceMap0259swap_checked fusedMap0259swap_checked
    DegreeOneSmallComparisons.comparison0259
#print axioms sourceMap0259swap_checked
#print axioms fusedMap0259swap_checked
#print axioms certified0259swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
