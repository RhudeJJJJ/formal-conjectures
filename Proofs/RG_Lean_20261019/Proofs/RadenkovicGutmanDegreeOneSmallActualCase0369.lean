/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0369 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0369 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0369 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0369_checked : acceptsGraphIso
    (source (graph core0369) (root 6) 0 3) DegreeOneSmallSpectrum575.graph sourceMap0369=true := by decide +kernel
theorem fusedMap0369_checked : acceptsGraphIso
    (fused (graph core0369) (root 6) 0 3) DegreeOneSmallSpectrum387.graph fusedMap0369=true := by decide +kernel
theorem certified0369 : Certified (graph core0369) (root 6) 0 3 :=
  of_native_maps core0369 DegreeOneSmallSpectrum575.graph DegreeOneSmallSpectrum387.graph
    sourceMap0369 fusedMap0369 sourceMap0369_checked fusedMap0369_checked
    DegreeOneSmallComparisons.comparison0369
#print axioms sourceMap0369_checked
#print axioms fusedMap0369_checked
#print axioms certified0369
def sourceMap0369swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0369swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0369swap_checked : acceptsGraphIso
    (source (graph core0369) (root 6) 3 0) DegreeOneSmallSpectrum575.graph sourceMap0369swap=true := by decide +kernel
theorem fusedMap0369swap_checked : acceptsGraphIso
    (fused (graph core0369) (root 6) 3 0) DegreeOneSmallSpectrum387.graph fusedMap0369swap=true := by decide +kernel
theorem certified0369swap : Certified (graph core0369) (root 6) 3 0 :=
  of_native_maps core0369 DegreeOneSmallSpectrum575.graph DegreeOneSmallSpectrum387.graph
    sourceMap0369swap fusedMap0369swap sourceMap0369swap_checked fusedMap0369swap_checked
    DegreeOneSmallComparisons.comparison0369
#print axioms sourceMap0369swap_checked
#print axioms fusedMap0369swap_checked
#print axioms certified0369swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
