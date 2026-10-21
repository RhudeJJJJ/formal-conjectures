/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0266 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0266 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,4,5,6,7,8,1,2,3,9,10,11,12] (sourceLabel 5 2 3 v)
def fusedMap0266 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0266_checked : acceptsGraphIso
    (source (graph core0266) (root 5) 2 3) DegreeOneSmallSpectrum1464.graph sourceMap0266=true := by decide +kernel
theorem fusedMap0266_checked : acceptsGraphIso
    (fused (graph core0266) (root 5) 2 3) DegreeOneSmallSpectrum862.graph fusedMap0266=true := by decide +kernel
theorem certified0266 : Certified (graph core0266) (root 5) 2 3 :=
  of_native_maps core0266 DegreeOneSmallSpectrum1464.graph DegreeOneSmallSpectrum862.graph
    sourceMap0266 fusedMap0266 sourceMap0266_checked fusedMap0266_checked
    DegreeOneSmallComparisons.comparison0266
#print axioms sourceMap0266_checked
#print axioms fusedMap0266_checked
#print axioms certified0266
def sourceMap0266swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,4,5,6,7,8,9,10,11,12,1,2,3] (sourceLabel 5 3 2 v)
def fusedMap0266swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0266swap_checked : acceptsGraphIso
    (source (graph core0266) (root 5) 3 2) DegreeOneSmallSpectrum1464.graph sourceMap0266swap=true := by decide +kernel
theorem fusedMap0266swap_checked : acceptsGraphIso
    (fused (graph core0266) (root 5) 3 2) DegreeOneSmallSpectrum862.graph fusedMap0266swap=true := by decide +kernel
theorem certified0266swap : Certified (graph core0266) (root 5) 3 2 :=
  of_native_maps core0266 DegreeOneSmallSpectrum1464.graph DegreeOneSmallSpectrum862.graph
    sourceMap0266swap fusedMap0266swap sourceMap0266swap_checked fusedMap0266swap_checked
    DegreeOneSmallComparisons.comparison0266
#print axioms sourceMap0266swap_checked
#print axioms fusedMap0266swap_checked
#print axioms certified0266swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
