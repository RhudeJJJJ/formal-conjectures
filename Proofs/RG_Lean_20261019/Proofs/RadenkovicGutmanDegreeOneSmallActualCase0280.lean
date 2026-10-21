/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0280 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0280 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,12,7,8,9,10,11] (sourceLabel 6 0 4 v)
def fusedMap0280 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0280_checked : acceptsGraphIso
    (source (graph core0280) (root 6) 0 4) DegreeOneSmallSpectrum908.graph sourceMap0280=true := by decide +kernel
theorem fusedMap0280_checked : acceptsGraphIso
    (fused (graph core0280) (root 6) 0 4) DegreeOneSmallSpectrum856.graph fusedMap0280=true := by decide +kernel
theorem certified0280 : Certified (graph core0280) (root 6) 0 4 :=
  of_native_maps core0280 DegreeOneSmallSpectrum908.graph DegreeOneSmallSpectrum856.graph
    sourceMap0280 fusedMap0280 sourceMap0280_checked fusedMap0280_checked
    DegreeOneSmallComparisons.comparison0280
#print axioms sourceMap0280_checked
#print axioms fusedMap0280_checked
#print axioms certified0280
def sourceMap0280swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 4 0 v)
def fusedMap0280swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0280swap_checked : acceptsGraphIso
    (source (graph core0280) (root 6) 4 0) DegreeOneSmallSpectrum908.graph sourceMap0280swap=true := by decide +kernel
theorem fusedMap0280swap_checked : acceptsGraphIso
    (fused (graph core0280) (root 6) 4 0) DegreeOneSmallSpectrum856.graph fusedMap0280swap=true := by decide +kernel
theorem certified0280swap : Certified (graph core0280) (root 6) 4 0 :=
  of_native_maps core0280 DegreeOneSmallSpectrum908.graph DegreeOneSmallSpectrum856.graph
    sourceMap0280swap fusedMap0280swap sourceMap0280swap_checked fusedMap0280swap_checked
    DegreeOneSmallComparisons.comparison0280
#print axioms sourceMap0280swap_checked
#print axioms fusedMap0280swap_checked
#print axioms certified0280swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
