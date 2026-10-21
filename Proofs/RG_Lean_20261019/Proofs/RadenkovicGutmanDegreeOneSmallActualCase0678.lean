/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0678 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0678 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0678 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0678_checked : acceptsGraphIso
    (source (graph core0678) (root 7) 0 3) DegreeOneSmallSpectrum988.graph sourceMap0678=true := by decide +kernel
theorem fusedMap0678_checked : acceptsGraphIso
    (fused (graph core0678) (root 7) 0 3) DegreeOneSmallSpectrum992.graph fusedMap0678=true := by decide +kernel
theorem certified0678 : Certified (graph core0678) (root 7) 0 3 :=
  of_native_maps core0678 DegreeOneSmallSpectrum988.graph DegreeOneSmallSpectrum992.graph
    sourceMap0678 fusedMap0678 sourceMap0678_checked fusedMap0678_checked
    DegreeOneSmallComparisons.comparison0678
#print axioms sourceMap0678_checked
#print axioms fusedMap0678_checked
#print axioms certified0678
def sourceMap0678swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0678swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0678swap_checked : acceptsGraphIso
    (source (graph core0678) (root 7) 3 0) DegreeOneSmallSpectrum988.graph sourceMap0678swap=true := by decide +kernel
theorem fusedMap0678swap_checked : acceptsGraphIso
    (fused (graph core0678) (root 7) 3 0) DegreeOneSmallSpectrum992.graph fusedMap0678swap=true := by decide +kernel
theorem certified0678swap : Certified (graph core0678) (root 7) 3 0 :=
  of_native_maps core0678 DegreeOneSmallSpectrum988.graph DegreeOneSmallSpectrum992.graph
    sourceMap0678swap fusedMap0678swap sourceMap0678swap_checked fusedMap0678swap_checked
    DegreeOneSmallComparisons.comparison0678
#print axioms sourceMap0678swap_checked
#print axioms fusedMap0678swap_checked
#print axioms certified0678swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
