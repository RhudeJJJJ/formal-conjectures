/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0174 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0174 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (sourceLabel 5 0 3 v)
def fusedMap0174 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0174_checked : acceptsGraphIso
    (source (graph core0174) (root 5) 0 3) DegreeOneSmallSpectrum197.graph sourceMap0174=true := by decide +kernel
theorem fusedMap0174_checked : acceptsGraphIso
    (fused (graph core0174) (root 5) 0 3) DegreeOneSmallSpectrum164.graph fusedMap0174=true := by decide +kernel
theorem certified0174 : Certified (graph core0174) (root 5) 0 3 :=
  of_native_maps core0174 DegreeOneSmallSpectrum197.graph DegreeOneSmallSpectrum164.graph
    sourceMap0174 fusedMap0174 sourceMap0174_checked fusedMap0174_checked
    DegreeOneSmallComparisons.comparison0174
#print axioms sourceMap0174_checked
#print axioms fusedMap0174_checked
#print axioms certified0174
def sourceMap0174swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 3 0 v)
def fusedMap0174swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0174swap_checked : acceptsGraphIso
    (source (graph core0174) (root 5) 3 0) DegreeOneSmallSpectrum197.graph sourceMap0174swap=true := by decide +kernel
theorem fusedMap0174swap_checked : acceptsGraphIso
    (fused (graph core0174) (root 5) 3 0) DegreeOneSmallSpectrum164.graph fusedMap0174swap=true := by decide +kernel
theorem certified0174swap : Certified (graph core0174) (root 5) 3 0 :=
  of_native_maps core0174 DegreeOneSmallSpectrum197.graph DegreeOneSmallSpectrum164.graph
    sourceMap0174swap fusedMap0174swap sourceMap0174swap_checked fusedMap0174swap_checked
    DegreeOneSmallComparisons.comparison0174
#print axioms sourceMap0174swap_checked
#print axioms fusedMap0174swap_checked
#print axioms certified0174swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
