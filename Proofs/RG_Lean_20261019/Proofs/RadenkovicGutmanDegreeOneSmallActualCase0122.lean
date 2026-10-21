/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0122 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0122 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap0122 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap0122_checked : acceptsGraphIso
    (source (graph core0122) (root 4) 1 5) DegreeOneSmallSpectrum880.graph sourceMap0122=true := by decide +kernel
theorem fusedMap0122_checked : acceptsGraphIso
    (fused (graph core0122) (root 4) 1 5) DegreeOneSmallSpectrum856.graph fusedMap0122=true := by decide +kernel
theorem certified0122 : Certified (graph core0122) (root 4) 1 5 :=
  of_native_maps core0122 DegreeOneSmallSpectrum880.graph DegreeOneSmallSpectrum856.graph
    sourceMap0122 fusedMap0122 sourceMap0122_checked fusedMap0122_checked
    DegreeOneSmallComparisons.comparison0122
#print axioms sourceMap0122_checked
#print axioms fusedMap0122_checked
#print axioms certified0122
def sourceMap0122swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,12,6,7] (sourceLabel 4 5 1 v)
def fusedMap0122swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap0122swap_checked : acceptsGraphIso
    (source (graph core0122) (root 4) 5 1) DegreeOneSmallSpectrum880.graph sourceMap0122swap=true := by decide +kernel
theorem fusedMap0122swap_checked : acceptsGraphIso
    (fused (graph core0122) (root 4) 5 1) DegreeOneSmallSpectrum856.graph fusedMap0122swap=true := by decide +kernel
theorem certified0122swap : Certified (graph core0122) (root 4) 5 1 :=
  of_native_maps core0122 DegreeOneSmallSpectrum880.graph DegreeOneSmallSpectrum856.graph
    sourceMap0122swap fusedMap0122swap sourceMap0122swap_checked fusedMap0122swap_checked
    DegreeOneSmallComparisons.comparison0122
#print axioms sourceMap0122swap_checked
#print axioms fusedMap0122swap_checked
#print axioms certified0122swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
