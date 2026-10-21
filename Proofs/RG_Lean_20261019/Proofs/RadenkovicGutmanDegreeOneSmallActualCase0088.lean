/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0088 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0088 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 3 1 6 v)
def fusedMap0088 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 1 6 v)
theorem sourceMap0088_checked : acceptsGraphIso
    (source (graph core0088) (root 3) 1 6) DegreeOneSmallSpectrum871.graph sourceMap0088=true := by decide +kernel
theorem fusedMap0088_checked : acceptsGraphIso
    (fused (graph core0088) (root 3) 1 6) DegreeOneSmallSpectrum856.graph fusedMap0088=true := by decide +kernel
theorem certified0088 : Certified (graph core0088) (root 3) 1 6 :=
  of_native_maps core0088 DegreeOneSmallSpectrum871.graph DegreeOneSmallSpectrum856.graph
    sourceMap0088 fusedMap0088 sourceMap0088_checked fusedMap0088_checked
    DegreeOneSmallComparisons.comparison0088
#print axioms sourceMap0088_checked
#print axioms fusedMap0088_checked
#print axioms certified0088
def sourceMap0088swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,3,4,5,1,0,8,9,10,11,12,6,7] (sourceLabel 3 6 1 v)
def fusedMap0088swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 6 1 v)
theorem sourceMap0088swap_checked : acceptsGraphIso
    (source (graph core0088) (root 3) 6 1) DegreeOneSmallSpectrum871.graph sourceMap0088swap=true := by decide +kernel
theorem fusedMap0088swap_checked : acceptsGraphIso
    (fused (graph core0088) (root 3) 6 1) DegreeOneSmallSpectrum856.graph fusedMap0088swap=true := by decide +kernel
theorem certified0088swap : Certified (graph core0088) (root 3) 6 1 :=
  of_native_maps core0088 DegreeOneSmallSpectrum871.graph DegreeOneSmallSpectrum856.graph
    sourceMap0088swap fusedMap0088swap sourceMap0088swap_checked fusedMap0088swap_checked
    DegreeOneSmallComparisons.comparison0088
#print axioms sourceMap0088swap_checked
#print axioms fusedMap0088swap_checked
#print axioms certified0088swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
