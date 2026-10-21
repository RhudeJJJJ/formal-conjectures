/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0186 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0186 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (sourceLabel 5 0 3 v)
def fusedMap0186 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0186_checked : acceptsGraphIso
    (source (graph core0186) (root 5) 0 3) DegreeOneSmallSpectrum217.graph sourceMap0186=true := by decide +kernel
theorem fusedMap0186_checked : acceptsGraphIso
    (fused (graph core0186) (root 5) 0 3) DegreeOneSmallSpectrum165.graph fusedMap0186=true := by decide +kernel
theorem certified0186 : Certified (graph core0186) (root 5) 0 3 :=
  of_native_maps core0186 DegreeOneSmallSpectrum217.graph DegreeOneSmallSpectrum165.graph
    sourceMap0186 fusedMap0186 sourceMap0186_checked fusedMap0186_checked
    DegreeOneSmallComparisons.comparison0186
#print axioms sourceMap0186_checked
#print axioms fusedMap0186_checked
#print axioms certified0186
def sourceMap0186swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 3 0 v)
def fusedMap0186swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0186swap_checked : acceptsGraphIso
    (source (graph core0186) (root 5) 3 0) DegreeOneSmallSpectrum217.graph sourceMap0186swap=true := by decide +kernel
theorem fusedMap0186swap_checked : acceptsGraphIso
    (fused (graph core0186) (root 5) 3 0) DegreeOneSmallSpectrum165.graph fusedMap0186swap=true := by decide +kernel
theorem certified0186swap : Certified (graph core0186) (root 5) 3 0 :=
  of_native_maps core0186 DegreeOneSmallSpectrum217.graph DegreeOneSmallSpectrum165.graph
    sourceMap0186swap fusedMap0186swap sourceMap0186swap_checked fusedMap0186swap_checked
    DegreeOneSmallComparisons.comparison0186
#print axioms sourceMap0186swap_checked
#print axioms fusedMap0186swap_checked
#print axioms certified0186swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
