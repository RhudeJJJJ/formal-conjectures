/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0558 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0558 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0558 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0558_checked : acceptsGraphIso
    (source (graph core0558) (root 7) 0 3) DegreeOneSmallSpectrum973.graph sourceMap0558=true := by decide +kernel
theorem fusedMap0558_checked : acceptsGraphIso
    (fused (graph core0558) (root 7) 0 3) DegreeOneSmallSpectrum974.graph fusedMap0558=true := by decide +kernel
theorem certified0558 : Certified (graph core0558) (root 7) 0 3 :=
  of_native_maps core0558 DegreeOneSmallSpectrum973.graph DegreeOneSmallSpectrum974.graph
    sourceMap0558 fusedMap0558 sourceMap0558_checked fusedMap0558_checked
    DegreeOneSmallComparisons.comparison0558
#print axioms sourceMap0558_checked
#print axioms fusedMap0558_checked
#print axioms certified0558
def sourceMap0558swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0558swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0558swap_checked : acceptsGraphIso
    (source (graph core0558) (root 7) 3 0) DegreeOneSmallSpectrum973.graph sourceMap0558swap=true := by decide +kernel
theorem fusedMap0558swap_checked : acceptsGraphIso
    (fused (graph core0558) (root 7) 3 0) DegreeOneSmallSpectrum974.graph fusedMap0558swap=true := by decide +kernel
theorem certified0558swap : Certified (graph core0558) (root 7) 3 0 :=
  of_native_maps core0558 DegreeOneSmallSpectrum973.graph DegreeOneSmallSpectrum974.graph
    sourceMap0558swap fusedMap0558swap sourceMap0558swap_checked fusedMap0558swap_checked
    DegreeOneSmallComparisons.comparison0558
#print axioms sourceMap0558swap_checked
#print axioms fusedMap0558swap_checked
#print axioms certified0558swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
