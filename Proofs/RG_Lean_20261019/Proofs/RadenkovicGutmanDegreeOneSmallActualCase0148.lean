/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0148 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0148 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap0148 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap0148_checked : acceptsGraphIso
    (source (graph core0148) (root 4) 0 5) DegreeOneSmallSpectrum411.graph sourceMap0148=true := by decide +kernel
theorem fusedMap0148_checked : acceptsGraphIso
    (fused (graph core0148) (root 4) 0 5) DegreeOneSmallSpectrum370.graph fusedMap0148=true := by decide +kernel
theorem certified0148 : Certified (graph core0148) (root 4) 0 5 :=
  of_native_maps core0148 DegreeOneSmallSpectrum411.graph DegreeOneSmallSpectrum370.graph
    sourceMap0148 fusedMap0148 sourceMap0148_checked fusedMap0148_checked
    DegreeOneSmallComparisons.comparison0148
#print axioms sourceMap0148_checked
#print axioms fusedMap0148_checked
#print axioms certified0148
def sourceMap0148swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,7] (sourceLabel 4 5 0 v)
def fusedMap0148swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap0148swap_checked : acceptsGraphIso
    (source (graph core0148) (root 4) 5 0) DegreeOneSmallSpectrum411.graph sourceMap0148swap=true := by decide +kernel
theorem fusedMap0148swap_checked : acceptsGraphIso
    (fused (graph core0148) (root 4) 5 0) DegreeOneSmallSpectrum370.graph fusedMap0148swap=true := by decide +kernel
theorem certified0148swap : Certified (graph core0148) (root 4) 5 0 :=
  of_native_maps core0148 DegreeOneSmallSpectrum411.graph DegreeOneSmallSpectrum370.graph
    sourceMap0148swap fusedMap0148swap sourceMap0148swap_checked fusedMap0148swap_checked
    DegreeOneSmallComparisons.comparison0148
#print axioms sourceMap0148swap_checked
#print axioms fusedMap0148swap_checked
#print axioms certified0148swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
