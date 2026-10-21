/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0352 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0352 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0352 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0352_checked : acceptsGraphIso
    (source (graph core0352) (root 6) 0 4) DegreeOneSmallSpectrum918.graph sourceMap0352=true := by decide +kernel
theorem fusedMap0352_checked : acceptsGraphIso
    (fused (graph core0352) (root 6) 0 4) DegreeOneSmallSpectrum922.graph fusedMap0352=true := by decide +kernel
theorem certified0352 : Certified (graph core0352) (root 6) 0 4 :=
  of_native_maps core0352 DegreeOneSmallSpectrum918.graph DegreeOneSmallSpectrum922.graph
    sourceMap0352 fusedMap0352 sourceMap0352_checked fusedMap0352_checked
    DegreeOneSmallComparisons.comparison0352
#print axioms sourceMap0352_checked
#print axioms fusedMap0352_checked
#print axioms certified0352
def sourceMap0352swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0352swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0352swap_checked : acceptsGraphIso
    (source (graph core0352) (root 6) 4 0) DegreeOneSmallSpectrum918.graph sourceMap0352swap=true := by decide +kernel
theorem fusedMap0352swap_checked : acceptsGraphIso
    (fused (graph core0352) (root 6) 4 0) DegreeOneSmallSpectrum922.graph fusedMap0352swap=true := by decide +kernel
theorem certified0352swap : Certified (graph core0352) (root 6) 4 0 :=
  of_native_maps core0352 DegreeOneSmallSpectrum918.graph DegreeOneSmallSpectrum922.graph
    sourceMap0352swap fusedMap0352swap sourceMap0352swap_checked fusedMap0352swap_checked
    DegreeOneSmallComparisons.comparison0352
#print axioms sourceMap0352swap_checked
#print axioms fusedMap0352swap_checked
#print axioms certified0352swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
