/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0094 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0094 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,5,6,7,1,2,3,4,8,9,10,11,12] (sourceLabel 3 3 4 v)
def fusedMap0094 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 3 4 v)
theorem sourceMap0094_checked : acceptsGraphIso
    (source (graph core0094) (root 3) 3 4) DegreeOneSmallSpectrum968.graph sourceMap0094=true := by decide +kernel
theorem fusedMap0094_checked : acceptsGraphIso
    (fused (graph core0094) (root 3) 3 4) DegreeOneSmallSpectrum856.graph fusedMap0094=true := by decide +kernel
theorem certified0094 : Certified (graph core0094) (root 3) 3 4 :=
  of_native_maps core0094 DegreeOneSmallSpectrum968.graph DegreeOneSmallSpectrum856.graph
    sourceMap0094 fusedMap0094 sourceMap0094_checked fusedMap0094_checked
    DegreeOneSmallComparisons.comparison0094
#print axioms sourceMap0094_checked
#print axioms fusedMap0094_checked
#print axioms certified0094
def sourceMap0094swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,5,6,7,8,9,10,11,12,1,2,3,4] (sourceLabel 3 4 3 v)
def fusedMap0094swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 4 3 v)
theorem sourceMap0094swap_checked : acceptsGraphIso
    (source (graph core0094) (root 3) 4 3) DegreeOneSmallSpectrum968.graph sourceMap0094swap=true := by decide +kernel
theorem fusedMap0094swap_checked : acceptsGraphIso
    (fused (graph core0094) (root 3) 4 3) DegreeOneSmallSpectrum856.graph fusedMap0094swap=true := by decide +kernel
theorem certified0094swap : Certified (graph core0094) (root 3) 4 3 :=
  of_native_maps core0094 DegreeOneSmallSpectrum968.graph DegreeOneSmallSpectrum856.graph
    sourceMap0094swap fusedMap0094swap sourceMap0094swap_checked fusedMap0094swap_checked
    DegreeOneSmallComparisons.comparison0094
#print axioms sourceMap0094swap_checked
#print axioms fusedMap0094swap_checked
#print axioms certified0094swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
