/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0933 : Family 8 := level8.get ⟨66,by decide⟩
def sourceMap0933 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,10,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap0933 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0933_checked : acceptsGraphIso
    (source (graph core0933) (root 8) 0 2) DegreeOneSmallSpectrum1451.graph sourceMap0933=true := by decide +kernel
theorem fusedMap0933_checked : acceptsGraphIso
    (fused (graph core0933) (root 8) 0 2) DegreeOneSmallSpectrum931.graph fusedMap0933=true := by decide +kernel
theorem certified0933 : Certified (graph core0933) (root 8) 0 2 :=
  of_native_maps core0933 DegreeOneSmallSpectrum1451.graph DegreeOneSmallSpectrum931.graph
    sourceMap0933 fusedMap0933 sourceMap0933_checked fusedMap0933_checked
    DegreeOneSmallComparisons.comparison0933
#print axioms sourceMap0933_checked
#print axioms fusedMap0933_checked
#print axioms certified0933
def sourceMap0933swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 8 2 0 v)
def fusedMap0933swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0933swap_checked : acceptsGraphIso
    (source (graph core0933) (root 8) 2 0) DegreeOneSmallSpectrum1451.graph sourceMap0933swap=true := by decide +kernel
theorem fusedMap0933swap_checked : acceptsGraphIso
    (fused (graph core0933) (root 8) 2 0) DegreeOneSmallSpectrum931.graph fusedMap0933swap=true := by decide +kernel
theorem certified0933swap : Certified (graph core0933) (root 8) 2 0 :=
  of_native_maps core0933 DegreeOneSmallSpectrum1451.graph DegreeOneSmallSpectrum931.graph
    sourceMap0933swap fusedMap0933swap sourceMap0933swap_checked fusedMap0933swap_checked
    DegreeOneSmallComparisons.comparison0933
#print axioms sourceMap0933swap_checked
#print axioms fusedMap0933swap_checked
#print axioms certified0933swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
