/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0988 : Family 8 := level8.get ⟨96,by decide⟩
def sourceMap0988 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0988 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0988_checked : acceptsGraphIso
    (source (graph core0988) (root 8) 0 1) DegreeOneSmallSpectrum616.graph sourceMap0988=true := by decide +kernel
theorem fusedMap0988_checked : acceptsGraphIso
    (fused (graph core0988) (root 8) 0 1) DegreeOneSmallSpectrum399.graph fusedMap0988=true := by decide +kernel
theorem certified0988 : Certified (graph core0988) (root 8) 0 1 :=
  of_native_maps core0988 DegreeOneSmallSpectrum616.graph DegreeOneSmallSpectrum399.graph
    sourceMap0988 fusedMap0988 sourceMap0988_checked fusedMap0988_checked
    DegreeOneSmallComparisons.comparison0988
#print axioms sourceMap0988_checked
#print axioms fusedMap0988_checked
#print axioms certified0988
def sourceMap0988swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0988swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0988swap_checked : acceptsGraphIso
    (source (graph core0988) (root 8) 1 0) DegreeOneSmallSpectrum616.graph sourceMap0988swap=true := by decide +kernel
theorem fusedMap0988swap_checked : acceptsGraphIso
    (fused (graph core0988) (root 8) 1 0) DegreeOneSmallSpectrum399.graph fusedMap0988swap=true := by decide +kernel
theorem certified0988swap : Certified (graph core0988) (root 8) 1 0 :=
  of_native_maps core0988 DegreeOneSmallSpectrum616.graph DegreeOneSmallSpectrum399.graph
    sourceMap0988swap fusedMap0988swap sourceMap0988swap_checked fusedMap0988swap_checked
    DegreeOneSmallComparisons.comparison0988
#print axioms sourceMap0988swap_checked
#print axioms fusedMap0988swap_checked
#print axioms certified0988swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
