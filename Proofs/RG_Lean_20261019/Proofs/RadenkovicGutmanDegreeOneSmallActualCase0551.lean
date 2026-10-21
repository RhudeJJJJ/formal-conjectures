/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0551 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0551 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap0551 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0551_checked : acceptsGraphIso
    (source (graph core0551) (root 7) 0 2) DegreeOneSmallSpectrum583.graph sourceMap0551=true := by decide +kernel
theorem fusedMap0551_checked : acceptsGraphIso
    (fused (graph core0551) (root 7) 0 2) DegreeOneSmallSpectrum393.graph fusedMap0551=true := by decide +kernel
theorem certified0551 : Certified (graph core0551) (root 7) 0 2 :=
  of_native_maps core0551 DegreeOneSmallSpectrum583.graph DegreeOneSmallSpectrum393.graph
    sourceMap0551 fusedMap0551 sourceMap0551_checked fusedMap0551_checked
    DegreeOneSmallComparisons.comparison0551
#print axioms sourceMap0551_checked
#print axioms fusedMap0551_checked
#print axioms certified0551
def sourceMap0551swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 2 0 v)
def fusedMap0551swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0551swap_checked : acceptsGraphIso
    (source (graph core0551) (root 7) 2 0) DegreeOneSmallSpectrum583.graph sourceMap0551swap=true := by decide +kernel
theorem fusedMap0551swap_checked : acceptsGraphIso
    (fused (graph core0551) (root 7) 2 0) DegreeOneSmallSpectrum393.graph fusedMap0551swap=true := by decide +kernel
theorem certified0551swap : Certified (graph core0551) (root 7) 2 0 :=
  of_native_maps core0551 DegreeOneSmallSpectrum583.graph DegreeOneSmallSpectrum393.graph
    sourceMap0551swap fusedMap0551swap sourceMap0551swap_checked fusedMap0551swap_checked
    DegreeOneSmallComparisons.comparison0551
#print axioms sourceMap0551swap_checked
#print axioms fusedMap0551swap_checked
#print axioms certified0551swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
