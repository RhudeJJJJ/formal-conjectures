/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0450 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0450 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 7 0 3 v)
def fusedMap0450 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 7 0 3 v)
theorem sourceMap0450_checked : acceptsGraphIso
    (source (graph core0450) (root 7) 0 3) DegreeOneSmallSpectrum859.graph sourceMap0450=true := by decide +kernel
theorem fusedMap0450_checked : acceptsGraphIso
    (fused (graph core0450) (root 7) 0 3) DegreeOneSmallSpectrum861.graph fusedMap0450=true := by decide +kernel
theorem certified0450 : Certified (graph core0450) (root 7) 0 3 :=
  of_native_maps core0450 DegreeOneSmallSpectrum859.graph DegreeOneSmallSpectrum861.graph
    sourceMap0450 fusedMap0450 sourceMap0450_checked fusedMap0450_checked
    DegreeOneSmallComparisons.comparison0450
#print axioms sourceMap0450_checked
#print axioms fusedMap0450_checked
#print axioms certified0450
def sourceMap0450swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 3 0 v)
def fusedMap0450swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 7 3 0 v)
theorem sourceMap0450swap_checked : acceptsGraphIso
    (source (graph core0450) (root 7) 3 0) DegreeOneSmallSpectrum859.graph sourceMap0450swap=true := by decide +kernel
theorem fusedMap0450swap_checked : acceptsGraphIso
    (fused (graph core0450) (root 7) 3 0) DegreeOneSmallSpectrum861.graph fusedMap0450swap=true := by decide +kernel
theorem certified0450swap : Certified (graph core0450) (root 7) 3 0 :=
  of_native_maps core0450 DegreeOneSmallSpectrum859.graph DegreeOneSmallSpectrum861.graph
    sourceMap0450swap fusedMap0450swap sourceMap0450swap_checked fusedMap0450swap_checked
    DegreeOneSmallComparisons.comparison0450
#print axioms sourceMap0450swap_checked
#print axioms fusedMap0450swap_checked
#print axioms certified0450swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
