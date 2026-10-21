/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0436 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0436 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0436 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0436_checked : acceptsGraphIso
    (source (graph core0436) (root 6) 1 3) DegreeOneSmallSpectrum1354.graph sourceMap0436=true := by decide +kernel
theorem fusedMap0436_checked : acceptsGraphIso
    (fused (graph core0436) (root 6) 1 3) DegreeOneSmallSpectrum916.graph fusedMap0436=true := by decide +kernel
theorem certified0436 : Certified (graph core0436) (root 6) 1 3 :=
  of_native_maps core0436 DegreeOneSmallSpectrum1354.graph DegreeOneSmallSpectrum916.graph
    sourceMap0436 fusedMap0436 sourceMap0436_checked fusedMap0436_checked
    DegreeOneSmallComparisons.comparison0436
#print axioms sourceMap0436_checked
#print axioms fusedMap0436_checked
#print axioms certified0436
def sourceMap0436swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,7,8] (sourceLabel 6 3 1 v)
def fusedMap0436swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0436swap_checked : acceptsGraphIso
    (source (graph core0436) (root 6) 3 1) DegreeOneSmallSpectrum1354.graph sourceMap0436swap=true := by decide +kernel
theorem fusedMap0436swap_checked : acceptsGraphIso
    (fused (graph core0436) (root 6) 3 1) DegreeOneSmallSpectrum916.graph fusedMap0436swap=true := by decide +kernel
theorem certified0436swap : Certified (graph core0436) (root 6) 3 1 :=
  of_native_maps core0436 DegreeOneSmallSpectrum1354.graph DegreeOneSmallSpectrum916.graph
    sourceMap0436swap fusedMap0436swap sourceMap0436swap_checked fusedMap0436swap_checked
    DegreeOneSmallComparisons.comparison0436
#print axioms sourceMap0436swap_checked
#print axioms fusedMap0436swap_checked
#print axioms certified0436swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
