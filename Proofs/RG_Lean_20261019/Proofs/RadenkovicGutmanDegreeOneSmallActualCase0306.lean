/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0306 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0306 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,5,1,2,3,4] (sourceLabel 6 0 3 v)
def fusedMap0306 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0306_checked : acceptsGraphIso
    (source (graph core0306) (root 6) 0 3) DegreeOneSmallSpectrum395.graph sourceMap0306=true := by decide +kernel
theorem fusedMap0306_checked : acceptsGraphIso
    (fused (graph core0306) (root 6) 0 3) DegreeOneSmallSpectrum396.graph fusedMap0306=true := by decide +kernel
theorem certified0306 : Certified (graph core0306) (root 6) 0 3 :=
  of_native_maps core0306 DegreeOneSmallSpectrum395.graph DegreeOneSmallSpectrum396.graph
    sourceMap0306 fusedMap0306 sourceMap0306_checked fusedMap0306_checked
    DegreeOneSmallComparisons.comparison0306
#print axioms sourceMap0306_checked
#print axioms fusedMap0306_checked
#print axioms certified0306
def sourceMap0306swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 6 3 0 v)
def fusedMap0306swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0306swap_checked : acceptsGraphIso
    (source (graph core0306) (root 6) 3 0) DegreeOneSmallSpectrum395.graph sourceMap0306swap=true := by decide +kernel
theorem fusedMap0306swap_checked : acceptsGraphIso
    (fused (graph core0306) (root 6) 3 0) DegreeOneSmallSpectrum396.graph fusedMap0306swap=true := by decide +kernel
theorem certified0306swap : Certified (graph core0306) (root 6) 3 0 :=
  of_native_maps core0306 DegreeOneSmallSpectrum395.graph DegreeOneSmallSpectrum396.graph
    sourceMap0306swap fusedMap0306swap sourceMap0306swap_checked fusedMap0306swap_checked
    DegreeOneSmallComparisons.comparison0306
#print axioms sourceMap0306swap_checked
#print axioms fusedMap0306swap_checked
#print axioms certified0306swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
