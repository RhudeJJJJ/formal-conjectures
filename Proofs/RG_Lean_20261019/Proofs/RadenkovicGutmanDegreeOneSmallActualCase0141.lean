/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0141 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0141 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap0141 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap0141_checked : acceptsGraphIso
    (source (graph core0141) (root 4) 2 4) DegreeOneSmallSpectrum1398.graph sourceMap0141=true := by decide +kernel
theorem fusedMap0141_checked : acceptsGraphIso
    (fused (graph core0141) (root 4) 2 4) DegreeOneSmallSpectrum857.graph fusedMap0141=true := by decide +kernel
theorem certified0141 : Certified (graph core0141) (root 4) 2 4 :=
  of_native_maps core0141 DegreeOneSmallSpectrum1398.graph DegreeOneSmallSpectrum857.graph
    sourceMap0141 fusedMap0141 sourceMap0141_checked fusedMap0141_checked
    DegreeOneSmallComparisons.comparison0141
#print axioms sourceMap0141_checked
#print axioms fusedMap0141_checked
#print axioms certified0141
def sourceMap0141swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,2,3,4,5,0,9,10,11,12,6,7,8] (sourceLabel 4 4 2 v)
def fusedMap0141swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap0141swap_checked : acceptsGraphIso
    (source (graph core0141) (root 4) 4 2) DegreeOneSmallSpectrum1398.graph sourceMap0141swap=true := by decide +kernel
theorem fusedMap0141swap_checked : acceptsGraphIso
    (fused (graph core0141) (root 4) 4 2) DegreeOneSmallSpectrum857.graph fusedMap0141swap=true := by decide +kernel
theorem certified0141swap : Certified (graph core0141) (root 4) 4 2 :=
  of_native_maps core0141 DegreeOneSmallSpectrum1398.graph DegreeOneSmallSpectrum857.graph
    sourceMap0141swap fusedMap0141swap sourceMap0141swap_checked fusedMap0141swap_checked
    DegreeOneSmallComparisons.comparison0141
#print axioms sourceMap0141swap_checked
#print axioms fusedMap0141swap_checked
#print axioms certified0141swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
