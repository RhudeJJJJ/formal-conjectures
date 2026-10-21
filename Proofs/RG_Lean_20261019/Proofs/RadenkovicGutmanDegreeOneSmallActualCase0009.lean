/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0009 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0009 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (sourceLabel 1 0 9 v)
def fusedMap0009 : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 0 9 v)
theorem sourceMap0009_checked : acceptsGraphIso
    (source (graph core0009) (root 1) 0 9) DegreeOneSmallSpectrum856.graph sourceMap0009=true := by decide +kernel
theorem fusedMap0009_checked : acceptsGraphIso
    (fused (graph core0009) (root 1) 0 9) DegreeOneSmallSpectrum861.graph fusedMap0009=true := by decide +kernel
theorem certified0009 : Certified (graph core0009) (root 1) 0 9 :=
  of_native_maps core0009 DegreeOneSmallSpectrum856.graph DegreeOneSmallSpectrum861.graph
    sourceMap0009 fusedMap0009 sourceMap0009_checked fusedMap0009_checked
    DegreeOneSmallComparisons.comparison0009
#print axioms sourceMap0009_checked
#print axioms fusedMap0009_checked
#print axioms certified0009
def sourceMap0009swap : (Vertices 1 ⊕ Fin 10 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,5,3,2,1,0,7,8,9,10,11,12,6] (sourceLabel 1 9 0 v)
def fusedMap0009swap : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 9 0 v)
theorem sourceMap0009swap_checked : acceptsGraphIso
    (source (graph core0009) (root 1) 9 0) DegreeOneSmallSpectrum856.graph sourceMap0009swap=true := by decide +kernel
theorem fusedMap0009swap_checked : acceptsGraphIso
    (fused (graph core0009) (root 1) 9 0) DegreeOneSmallSpectrum861.graph fusedMap0009swap=true := by decide +kernel
theorem certified0009swap : Certified (graph core0009) (root 1) 9 0 :=
  of_native_maps core0009 DegreeOneSmallSpectrum856.graph DegreeOneSmallSpectrum861.graph
    sourceMap0009swap fusedMap0009swap sourceMap0009swap_checked fusedMap0009swap_checked
    DegreeOneSmallComparisons.comparison0009
#print axioms sourceMap0009swap_checked
#print axioms fusedMap0009swap_checked
#print axioms certified0009swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
