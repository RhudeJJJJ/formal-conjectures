/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0135 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0135 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7] (sourceLabel 4 1 2 v)
def fusedMap0135 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap0135_checked : acceptsGraphIso
    (source (graph core0135) (root 4) 1 2) DegreeOneSmallSpectrum144.graph sourceMap0135=true := by decide +kernel
theorem fusedMap0135_checked : acceptsGraphIso
    (fused (graph core0135) (root 4) 1 2) DegreeOneSmallSpectrum086.graph fusedMap0135=true := by decide +kernel
theorem certified0135 : Certified (graph core0135) (root 4) 1 2 :=
  of_native_maps core0135 DegreeOneSmallSpectrum144.graph DegreeOneSmallSpectrum086.graph
    sourceMap0135 fusedMap0135 sourceMap0135_checked fusedMap0135_checked
    DegreeOneSmallComparisons.comparison0135
#print axioms sourceMap0135_checked
#print axioms fusedMap0135_checked
#print axioms certified0135
def sourceMap0135swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 2 1 v)
def fusedMap0135swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap0135swap_checked : acceptsGraphIso
    (source (graph core0135) (root 4) 2 1) DegreeOneSmallSpectrum144.graph sourceMap0135swap=true := by decide +kernel
theorem fusedMap0135swap_checked : acceptsGraphIso
    (fused (graph core0135) (root 4) 2 1) DegreeOneSmallSpectrum086.graph fusedMap0135swap=true := by decide +kernel
theorem certified0135swap : Certified (graph core0135) (root 4) 2 1 :=
  of_native_maps core0135 DegreeOneSmallSpectrum144.graph DegreeOneSmallSpectrum086.graph
    sourceMap0135swap fusedMap0135swap sourceMap0135swap_checked fusedMap0135swap_checked
    DegreeOneSmallComparisons.comparison0135
#print axioms sourceMap0135swap_checked
#print axioms fusedMap0135swap_checked
#print axioms certified0135swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
