/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0301 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0301 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0301 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0301_checked : acceptsGraphIso
    (source (graph core0301) (root 6) 1 3) DegreeOneSmallSpectrum963.graph sourceMap0301=true := by decide +kernel
theorem fusedMap0301_checked : acceptsGraphIso
    (fused (graph core0301) (root 6) 1 3) DegreeOneSmallSpectrum858.graph fusedMap0301=true := by decide +kernel
theorem certified0301 : Certified (graph core0301) (root 6) 1 3 :=
  of_native_maps core0301 DegreeOneSmallSpectrum963.graph DegreeOneSmallSpectrum858.graph
    sourceMap0301 fusedMap0301 sourceMap0301_checked fusedMap0301_checked
    DegreeOneSmallComparisons.comparison0301
#print axioms sourceMap0301_checked
#print axioms fusedMap0301_checked
#print axioms certified0301
def sourceMap0301swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0301swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0301swap_checked : acceptsGraphIso
    (source (graph core0301) (root 6) 3 1) DegreeOneSmallSpectrum963.graph sourceMap0301swap=true := by decide +kernel
theorem fusedMap0301swap_checked : acceptsGraphIso
    (fused (graph core0301) (root 6) 3 1) DegreeOneSmallSpectrum858.graph fusedMap0301swap=true := by decide +kernel
theorem certified0301swap : Certified (graph core0301) (root 6) 3 1 :=
  of_native_maps core0301 DegreeOneSmallSpectrum963.graph DegreeOneSmallSpectrum858.graph
    sourceMap0301swap fusedMap0301swap sourceMap0301swap_checked fusedMap0301swap_checked
    DegreeOneSmallComparisons.comparison0301
#print axioms sourceMap0301swap_checked
#print axioms fusedMap0301swap_checked
#print axioms certified0301swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
