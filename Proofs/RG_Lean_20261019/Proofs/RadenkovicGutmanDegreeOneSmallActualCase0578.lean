/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0578 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0578 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0578 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0578_checked : acceptsGraphIso
    (source (graph core0578) (root 7) 1 2) DegreeOneSmallSpectrum1056.graph sourceMap0578=true := by decide +kernel
theorem fusedMap0578_checked : acceptsGraphIso
    (fused (graph core0578) (root 7) 1 2) DegreeOneSmallSpectrum864.graph fusedMap0578=true := by decide +kernel
theorem certified0578 : Certified (graph core0578) (root 7) 1 2 :=
  of_native_maps core0578 DegreeOneSmallSpectrum1056.graph DegreeOneSmallSpectrum864.graph
    sourceMap0578 fusedMap0578 sourceMap0578_checked fusedMap0578_checked
    DegreeOneSmallComparisons.comparison0578
#print axioms sourceMap0578_checked
#print axioms fusedMap0578_checked
#print axioms certified0578
def sourceMap0578swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0578swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0578swap_checked : acceptsGraphIso
    (source (graph core0578) (root 7) 2 1) DegreeOneSmallSpectrum1056.graph sourceMap0578swap=true := by decide +kernel
theorem fusedMap0578swap_checked : acceptsGraphIso
    (fused (graph core0578) (root 7) 2 1) DegreeOneSmallSpectrum864.graph fusedMap0578swap=true := by decide +kernel
theorem certified0578swap : Certified (graph core0578) (root 7) 2 1 :=
  of_native_maps core0578 DegreeOneSmallSpectrum1056.graph DegreeOneSmallSpectrum864.graph
    sourceMap0578swap fusedMap0578swap sourceMap0578swap_checked fusedMap0578swap_checked
    DegreeOneSmallComparisons.comparison0578
#print axioms sourceMap0578swap_checked
#print axioms fusedMap0578swap_checked
#print axioms certified0578swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
