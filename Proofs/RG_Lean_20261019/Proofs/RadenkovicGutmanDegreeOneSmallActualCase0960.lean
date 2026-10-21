/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0960 : Family 8 := level8.get ⟨78,by decide⟩
def sourceMap0960 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0960 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap0960_checked : acceptsGraphIso
    (source (graph core0960) (root 8) 0 1) DegreeOneSmallSpectrum539.graph sourceMap0960=true := by decide +kernel
theorem fusedMap0960_checked : acceptsGraphIso
    (fused (graph core0960) (root 8) 0 1) DegreeOneSmallSpectrum583.graph fusedMap0960=true := by decide +kernel
theorem certified0960 : Certified (graph core0960) (root 8) 0 1 :=
  of_native_maps core0960 DegreeOneSmallSpectrum539.graph DegreeOneSmallSpectrum583.graph
    sourceMap0960 fusedMap0960 sourceMap0960_checked fusedMap0960_checked
    DegreeOneSmallComparisons.comparison0960
#print axioms sourceMap0960_checked
#print axioms fusedMap0960_checked
#print axioms certified0960
def sourceMap0960swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0960swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap0960swap_checked : acceptsGraphIso
    (source (graph core0960) (root 8) 1 0) DegreeOneSmallSpectrum539.graph sourceMap0960swap=true := by decide +kernel
theorem fusedMap0960swap_checked : acceptsGraphIso
    (fused (graph core0960) (root 8) 1 0) DegreeOneSmallSpectrum583.graph fusedMap0960swap=true := by decide +kernel
theorem certified0960swap : Certified (graph core0960) (root 8) 1 0 :=
  of_native_maps core0960 DegreeOneSmallSpectrum539.graph DegreeOneSmallSpectrum583.graph
    sourceMap0960swap fusedMap0960swap sourceMap0960swap_checked fusedMap0960swap_checked
    DegreeOneSmallComparisons.comparison0960
#print axioms sourceMap0960swap_checked
#print axioms fusedMap0960swap_checked
#print axioms certified0960swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
