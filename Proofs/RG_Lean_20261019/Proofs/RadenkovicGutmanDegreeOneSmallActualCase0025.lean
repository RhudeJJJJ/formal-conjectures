/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0025 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0025 : (Vertices 1 ⊕ Fin 4 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,5,1,2,3,4,6,7,8,9,10] (sourceLabel 1 3 4 v)
def fusedMap0025 : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 3 4 v)
theorem sourceMap0025_checked : acceptsGraphIso
    (source (graph core0025) (root 1) 3 4) DegreeOneSmallSpectrum167.graph sourceMap0025=true := by decide +kernel
theorem fusedMap0025_checked : acceptsGraphIso
    (fused (graph core0025) (root 1) 3 4) DegreeOneSmallSpectrum168.graph fusedMap0025=true := by decide +kernel
theorem certified0025 : Certified (graph core0025) (root 1) 3 4 :=
  of_native_maps core0025 DegreeOneSmallSpectrum167.graph DegreeOneSmallSpectrum168.graph
    sourceMap0025 fusedMap0025 sourceMap0025_checked fusedMap0025_checked
    DegreeOneSmallComparisons.comparison0025
#print axioms sourceMap0025_checked
#print axioms fusedMap0025_checked
#print axioms certified0025
def sourceMap0025swap : (Vertices 1 ⊕ Fin 5 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4] (sourceLabel 1 4 3 v)
def fusedMap0025swap : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 4 3 v)
theorem sourceMap0025swap_checked : acceptsGraphIso
    (source (graph core0025) (root 1) 4 3) DegreeOneSmallSpectrum167.graph sourceMap0025swap=true := by decide +kernel
theorem fusedMap0025swap_checked : acceptsGraphIso
    (fused (graph core0025) (root 1) 4 3) DegreeOneSmallSpectrum168.graph fusedMap0025swap=true := by decide +kernel
theorem certified0025swap : Certified (graph core0025) (root 1) 4 3 :=
  of_native_maps core0025 DegreeOneSmallSpectrum167.graph DegreeOneSmallSpectrum168.graph
    sourceMap0025swap fusedMap0025swap sourceMap0025swap_checked fusedMap0025swap_checked
    DegreeOneSmallComparisons.comparison0025
#print axioms sourceMap0025swap_checked
#print axioms fusedMap0025swap_checked
#print axioms certified0025swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
