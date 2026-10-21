/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0722 : Family 7 := level7.get ⟨82,by decide⟩
def sourceMap0722 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0722 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0722_checked : acceptsGraphIso
    (source (graph core0722) (root 7) 1 2) DegreeOneSmallSpectrum1906.graph sourceMap0722=true := by decide +kernel
theorem fusedMap0722_checked : acceptsGraphIso
    (fused (graph core0722) (root 7) 1 2) DegreeOneSmallSpectrum1301.graph fusedMap0722=true := by decide +kernel
theorem certified0722 : Certified (graph core0722) (root 7) 1 2 :=
  of_native_maps core0722 DegreeOneSmallSpectrum1906.graph DegreeOneSmallSpectrum1301.graph
    sourceMap0722 fusedMap0722 sourceMap0722_checked fusedMap0722_checked
    DegreeOneSmallComparisons.comparison0722
#print axioms sourceMap0722_checked
#print axioms fusedMap0722_checked
#print axioms certified0722
def sourceMap0722swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0722swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0722swap_checked : acceptsGraphIso
    (source (graph core0722) (root 7) 2 1) DegreeOneSmallSpectrum1906.graph sourceMap0722swap=true := by decide +kernel
theorem fusedMap0722swap_checked : acceptsGraphIso
    (fused (graph core0722) (root 7) 2 1) DegreeOneSmallSpectrum1301.graph fusedMap0722swap=true := by decide +kernel
theorem certified0722swap : Certified (graph core0722) (root 7) 2 1 :=
  of_native_maps core0722 DegreeOneSmallSpectrum1906.graph DegreeOneSmallSpectrum1301.graph
    sourceMap0722swap fusedMap0722swap sourceMap0722swap_checked fusedMap0722swap_checked
    DegreeOneSmallComparisons.comparison0722
#print axioms sourceMap0722swap_checked
#print axioms fusedMap0722swap_checked
#print axioms certified0722swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
