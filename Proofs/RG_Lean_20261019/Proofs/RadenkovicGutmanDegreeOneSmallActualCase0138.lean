/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0138 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0138 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap0138 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap0138_checked : acceptsGraphIso
    (source (graph core0138) (root 4) 1 5) DegreeOneSmallSpectrum923.graph sourceMap0138=true := by decide +kernel
theorem fusedMap0138_checked : acceptsGraphIso
    (fused (graph core0138) (root 4) 1 5) DegreeOneSmallSpectrum857.graph fusedMap0138=true := by decide +kernel
theorem certified0138 : Certified (graph core0138) (root 4) 1 5 :=
  of_native_maps core0138 DegreeOneSmallSpectrum923.graph DegreeOneSmallSpectrum857.graph
    sourceMap0138 fusedMap0138 sourceMap0138_checked fusedMap0138_checked
    DegreeOneSmallComparisons.comparison0138
#print axioms sourceMap0138_checked
#print axioms fusedMap0138_checked
#print axioms certified0138
def sourceMap0138swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,12,6,7] (sourceLabel 4 5 1 v)
def fusedMap0138swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap0138swap_checked : acceptsGraphIso
    (source (graph core0138) (root 4) 5 1) DegreeOneSmallSpectrum923.graph sourceMap0138swap=true := by decide +kernel
theorem fusedMap0138swap_checked : acceptsGraphIso
    (fused (graph core0138) (root 4) 5 1) DegreeOneSmallSpectrum857.graph fusedMap0138swap=true := by decide +kernel
theorem certified0138swap : Certified (graph core0138) (root 4) 5 1 :=
  of_native_maps core0138 DegreeOneSmallSpectrum923.graph DegreeOneSmallSpectrum857.graph
    sourceMap0138swap fusedMap0138swap sourceMap0138swap_checked fusedMap0138swap_checked
    DegreeOneSmallComparisons.comparison0138
#print axioms sourceMap0138swap_checked
#print axioms fusedMap0138swap_checked
#print axioms certified0138swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
