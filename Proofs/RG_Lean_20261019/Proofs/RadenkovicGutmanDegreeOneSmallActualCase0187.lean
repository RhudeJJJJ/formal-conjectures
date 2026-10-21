/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0187 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0187 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0187 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0187_checked : acceptsGraphIso
    (source (graph core0187) (root 5) 0 4) DegreeOneSmallSpectrum382.graph sourceMap0187=true := by decide +kernel
theorem fusedMap0187_checked : acceptsGraphIso
    (fused (graph core0187) (root 5) 0 4) DegreeOneSmallSpectrum386.graph fusedMap0187=true := by decide +kernel
theorem certified0187 : Certified (graph core0187) (root 5) 0 4 :=
  of_native_maps core0187 DegreeOneSmallSpectrum382.graph DegreeOneSmallSpectrum386.graph
    sourceMap0187 fusedMap0187 sourceMap0187_checked fusedMap0187_checked
    DegreeOneSmallComparisons.comparison0187
#print axioms sourceMap0187_checked
#print axioms fusedMap0187_checked
#print axioms certified0187
def sourceMap0187swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,11,6] (sourceLabel 5 4 0 v)
def fusedMap0187swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0187swap_checked : acceptsGraphIso
    (source (graph core0187) (root 5) 4 0) DegreeOneSmallSpectrum382.graph sourceMap0187swap=true := by decide +kernel
theorem fusedMap0187swap_checked : acceptsGraphIso
    (fused (graph core0187) (root 5) 4 0) DegreeOneSmallSpectrum386.graph fusedMap0187swap=true := by decide +kernel
theorem certified0187swap : Certified (graph core0187) (root 5) 4 0 :=
  of_native_maps core0187 DegreeOneSmallSpectrum382.graph DegreeOneSmallSpectrum386.graph
    sourceMap0187swap fusedMap0187swap sourceMap0187swap_checked fusedMap0187swap_checked
    DegreeOneSmallComparisons.comparison0187
#print axioms sourceMap0187swap_checked
#print axioms fusedMap0187swap_checked
#print axioms certified0187swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
