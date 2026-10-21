/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0020 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0020 : (Vertices 1 ⊕ Fin 3 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,5,2,3,4,0,6,7,8,9] (sourceLabel 1 2 4 v)
def fusedMap0020 : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 2 4 v)
theorem sourceMap0020_checked : acceptsGraphIso
    (source (graph core0020) (root 1) 2 4) DegreeOneSmallSpectrum090.graph sourceMap0020=true := by decide +kernel
theorem fusedMap0020_checked : acceptsGraphIso
    (fused (graph core0020) (root 1) 2 4) DegreeOneSmallSpectrum073.graph fusedMap0020=true := by decide +kernel
theorem certified0020 : Certified (graph core0020) (root 1) 2 4 :=
  of_native_maps core0020 DegreeOneSmallSpectrum090.graph DegreeOneSmallSpectrum073.graph
    sourceMap0020 fusedMap0020 sourceMap0020_checked fusedMap0020_checked
    DegreeOneSmallComparisons.comparison0020
#print axioms sourceMap0020_checked
#print axioms fusedMap0020_checked
#print axioms certified0020
def sourceMap0020swap : (Vertices 1 ⊕ Fin 5 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,5,0,6,7,8,9,2,3,4] (sourceLabel 1 4 2 v)
def fusedMap0020swap : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 4 2 v)
theorem sourceMap0020swap_checked : acceptsGraphIso
    (source (graph core0020) (root 1) 4 2) DegreeOneSmallSpectrum090.graph sourceMap0020swap=true := by decide +kernel
theorem fusedMap0020swap_checked : acceptsGraphIso
    (fused (graph core0020) (root 1) 4 2) DegreeOneSmallSpectrum073.graph fusedMap0020swap=true := by decide +kernel
theorem certified0020swap : Certified (graph core0020) (root 1) 4 2 :=
  of_native_maps core0020 DegreeOneSmallSpectrum090.graph DegreeOneSmallSpectrum073.graph
    sourceMap0020swap fusedMap0020swap sourceMap0020swap_checked fusedMap0020swap_checked
    DegreeOneSmallComparisons.comparison0020
#print axioms sourceMap0020swap_checked
#print axioms fusedMap0020swap_checked
#print axioms certified0020swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
