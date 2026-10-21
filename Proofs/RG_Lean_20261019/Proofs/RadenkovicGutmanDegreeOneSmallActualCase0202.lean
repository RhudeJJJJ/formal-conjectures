/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0202 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0202 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,4,5,1,2,3] (sourceLabel 5 1 2 v)
def fusedMap0202 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0202_checked : acceptsGraphIso
    (source (graph core0202) (root 5) 1 2) DegreeOneSmallSpectrum221.graph sourceMap0202=true := by decide +kernel
theorem fusedMap0202_checked : acceptsGraphIso
    (fused (graph core0202) (root 5) 1 2) DegreeOneSmallSpectrum166.graph fusedMap0202=true := by decide +kernel
theorem certified0202 : Certified (graph core0202) (root 5) 1 2 :=
  of_native_maps core0202 DegreeOneSmallSpectrum221.graph DegreeOneSmallSpectrum166.graph
    sourceMap0202 fusedMap0202 sourceMap0202_checked fusedMap0202_checked
    DegreeOneSmallComparisons.comparison0202
#print axioms sourceMap0202_checked
#print axioms fusedMap0202_checked
#print axioms certified0202
def sourceMap0202swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 5 2 1 v)
def fusedMap0202swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0202swap_checked : acceptsGraphIso
    (source (graph core0202) (root 5) 2 1) DegreeOneSmallSpectrum221.graph sourceMap0202swap=true := by decide +kernel
theorem fusedMap0202swap_checked : acceptsGraphIso
    (fused (graph core0202) (root 5) 2 1) DegreeOneSmallSpectrum166.graph fusedMap0202swap=true := by decide +kernel
theorem certified0202swap : Certified (graph core0202) (root 5) 2 1 :=
  of_native_maps core0202 DegreeOneSmallSpectrum221.graph DegreeOneSmallSpectrum166.graph
    sourceMap0202swap fusedMap0202swap sourceMap0202swap_checked fusedMap0202swap_checked
    DegreeOneSmallComparisons.comparison0202
#print axioms sourceMap0202swap_checked
#print axioms fusedMap0202swap_checked
#print axioms certified0202swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
