/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0164 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0164 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0164 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0164_checked : acceptsGraphIso
    (source (graph core0164) (root 5) 0 5) DegreeOneSmallSpectrum860.graph sourceMap0164=true := by decide +kernel
theorem fusedMap0164_checked : acceptsGraphIso
    (fused (graph core0164) (root 5) 0 5) DegreeOneSmallSpectrum861.graph fusedMap0164=true := by decide +kernel
theorem certified0164 : Certified (graph core0164) (root 5) 0 5 :=
  of_native_maps core0164 DegreeOneSmallSpectrum860.graph DegreeOneSmallSpectrum861.graph
    sourceMap0164 fusedMap0164 sourceMap0164_checked fusedMap0164_checked
    DegreeOneSmallComparisons.comparison0164
#print axioms sourceMap0164_checked
#print axioms fusedMap0164_checked
#print axioms certified0164
def sourceMap0164swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,11,12,6] (sourceLabel 5 5 0 v)
def fusedMap0164swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0164swap_checked : acceptsGraphIso
    (source (graph core0164) (root 5) 5 0) DegreeOneSmallSpectrum860.graph sourceMap0164swap=true := by decide +kernel
theorem fusedMap0164swap_checked : acceptsGraphIso
    (fused (graph core0164) (root 5) 5 0) DegreeOneSmallSpectrum861.graph fusedMap0164swap=true := by decide +kernel
theorem certified0164swap : Certified (graph core0164) (root 5) 5 0 :=
  of_native_maps core0164 DegreeOneSmallSpectrum860.graph DegreeOneSmallSpectrum861.graph
    sourceMap0164swap fusedMap0164swap sourceMap0164swap_checked fusedMap0164swap_checked
    DegreeOneSmallComparisons.comparison0164
#print axioms sourceMap0164swap_checked
#print axioms fusedMap0164swap_checked
#print axioms certified0164swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
