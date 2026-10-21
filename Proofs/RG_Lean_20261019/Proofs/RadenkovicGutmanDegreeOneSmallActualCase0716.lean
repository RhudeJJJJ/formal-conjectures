/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0716 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0716 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0716 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0716_checked : acceptsGraphIso
    (source (graph core0716) (root 7) 1 2) DegreeOneSmallSpectrum1896.graph sourceMap0716=true := by decide +kernel
theorem fusedMap0716_checked : acceptsGraphIso
    (fused (graph core0716) (root 7) 1 2) DegreeOneSmallSpectrum1296.graph fusedMap0716=true := by decide +kernel
theorem certified0716 : Certified (graph core0716) (root 7) 1 2 :=
  of_native_maps core0716 DegreeOneSmallSpectrum1896.graph DegreeOneSmallSpectrum1296.graph
    sourceMap0716 fusedMap0716 sourceMap0716_checked fusedMap0716_checked
    DegreeOneSmallComparisons.comparison0716
#print axioms sourceMap0716_checked
#print axioms fusedMap0716_checked
#print axioms certified0716
def sourceMap0716swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0716swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0716swap_checked : acceptsGraphIso
    (source (graph core0716) (root 7) 2 1) DegreeOneSmallSpectrum1896.graph sourceMap0716swap=true := by decide +kernel
theorem fusedMap0716swap_checked : acceptsGraphIso
    (fused (graph core0716) (root 7) 2 1) DegreeOneSmallSpectrum1296.graph fusedMap0716swap=true := by decide +kernel
theorem certified0716swap : Certified (graph core0716) (root 7) 2 1 :=
  of_native_maps core0716 DegreeOneSmallSpectrum1896.graph DegreeOneSmallSpectrum1296.graph
    sourceMap0716swap fusedMap0716swap sourceMap0716swap_checked fusedMap0716swap_checked
    DegreeOneSmallComparisons.comparison0716
#print axioms sourceMap0716swap_checked
#print axioms fusedMap0716swap_checked
#print axioms certified0716swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
