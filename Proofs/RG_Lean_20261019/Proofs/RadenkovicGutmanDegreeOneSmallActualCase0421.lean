/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0421 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0421 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0421 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0421_checked : acceptsGraphIso
    (source (graph core0421) (root 6) 0 1) DegreeOneSmallSpectrum132.graph sourceMap0421=true := by decide +kernel
theorem fusedMap0421_checked : acceptsGraphIso
    (fused (graph core0421) (root 6) 0 1) DegreeOneSmallSpectrum133.graph fusedMap0421=true := by decide +kernel
theorem certified0421 : Certified (graph core0421) (root 6) 0 1 :=
  of_native_maps core0421 DegreeOneSmallSpectrum132.graph DegreeOneSmallSpectrum133.graph
    sourceMap0421 fusedMap0421 sourceMap0421_checked fusedMap0421_checked
    DegreeOneSmallComparisons.comparison0421
#print axioms sourceMap0421_checked
#print axioms fusedMap0421_checked
#print axioms certified0421
def sourceMap0421swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0421swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0421swap_checked : acceptsGraphIso
    (source (graph core0421) (root 6) 1 0) DegreeOneSmallSpectrum132.graph sourceMap0421swap=true := by decide +kernel
theorem fusedMap0421swap_checked : acceptsGraphIso
    (fused (graph core0421) (root 6) 1 0) DegreeOneSmallSpectrum133.graph fusedMap0421swap=true := by decide +kernel
theorem certified0421swap : Certified (graph core0421) (root 6) 1 0 :=
  of_native_maps core0421 DegreeOneSmallSpectrum132.graph DegreeOneSmallSpectrum133.graph
    sourceMap0421swap fusedMap0421swap sourceMap0421swap_checked fusedMap0421swap_checked
    DegreeOneSmallComparisons.comparison0421
#print axioms sourceMap0421swap_checked
#print axioms fusedMap0421swap_checked
#print axioms certified0421swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
