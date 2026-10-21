/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0260 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0260 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0260 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0260_checked : acceptsGraphIso
    (source (graph core0260) (root 5) 0 5) DegreeOneSmallSpectrum992.graph sourceMap0260=true := by decide +kernel
theorem fusedMap0260_checked : acceptsGraphIso
    (fused (graph core0260) (root 5) 0 5) DegreeOneSmallSpectrum862.graph fusedMap0260=true := by decide +kernel
theorem certified0260 : Certified (graph core0260) (root 5) 0 5 :=
  of_native_maps core0260 DegreeOneSmallSpectrum992.graph DegreeOneSmallSpectrum862.graph
    sourceMap0260 fusedMap0260 sourceMap0260_checked fusedMap0260_checked
    DegreeOneSmallComparisons.comparison0260
#print axioms sourceMap0260_checked
#print axioms fusedMap0260_checked
#print axioms certified0260
def sourceMap0260swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,8] (sourceLabel 5 5 0 v)
def fusedMap0260swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0260swap_checked : acceptsGraphIso
    (source (graph core0260) (root 5) 5 0) DegreeOneSmallSpectrum992.graph sourceMap0260swap=true := by decide +kernel
theorem fusedMap0260swap_checked : acceptsGraphIso
    (fused (graph core0260) (root 5) 5 0) DegreeOneSmallSpectrum862.graph fusedMap0260swap=true := by decide +kernel
theorem certified0260swap : Certified (graph core0260) (root 5) 5 0 :=
  of_native_maps core0260 DegreeOneSmallSpectrum992.graph DegreeOneSmallSpectrum862.graph
    sourceMap0260swap fusedMap0260swap sourceMap0260swap_checked fusedMap0260swap_checked
    DegreeOneSmallComparisons.comparison0260
#print axioms sourceMap0260swap_checked
#print axioms fusedMap0260swap_checked
#print axioms certified0260swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
