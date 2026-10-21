/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0194 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0194 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (sourceLabel 5 2 3 v)
def fusedMap0194 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0194_checked : acceptsGraphIso
    (source (graph core0194) (root 5) 2 3) DegreeOneSmallSpectrum1452.graph sourceMap0194=true := by decide +kernel
theorem fusedMap0194_checked : acceptsGraphIso
    (fused (graph core0194) (root 5) 2 3) DegreeOneSmallSpectrum857.graph fusedMap0194=true := by decide +kernel
theorem certified0194 : Certified (graph core0194) (root 5) 2 3 :=
  of_native_maps core0194 DegreeOneSmallSpectrum1452.graph DegreeOneSmallSpectrum857.graph
    sourceMap0194 fusedMap0194 sourceMap0194_checked fusedMap0194_checked
    DegreeOneSmallComparisons.comparison0194
#print axioms sourceMap0194_checked
#print axioms fusedMap0194_checked
#print axioms certified0194
def sourceMap0194swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 3 2 v)
def fusedMap0194swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0194swap_checked : acceptsGraphIso
    (source (graph core0194) (root 5) 3 2) DegreeOneSmallSpectrum1452.graph sourceMap0194swap=true := by decide +kernel
theorem fusedMap0194swap_checked : acceptsGraphIso
    (fused (graph core0194) (root 5) 3 2) DegreeOneSmallSpectrum857.graph fusedMap0194swap=true := by decide +kernel
theorem certified0194swap : Certified (graph core0194) (root 5) 3 2 :=
  of_native_maps core0194 DegreeOneSmallSpectrum1452.graph DegreeOneSmallSpectrum857.graph
    sourceMap0194swap fusedMap0194swap sourceMap0194swap_checked fusedMap0194swap_checked
    DegreeOneSmallComparisons.comparison0194
#print axioms sourceMap0194swap_checked
#print axioms fusedMap0194swap_checked
#print axioms certified0194swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
