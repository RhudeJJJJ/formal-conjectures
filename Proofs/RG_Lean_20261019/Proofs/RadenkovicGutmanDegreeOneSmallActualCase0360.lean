/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0360 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0360 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0360 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0360_checked : acceptsGraphIso
    (source (graph core0360) (root 6) 0 3) DegreeOneSmallSpectrum550.graph sourceMap0360=true := by decide +kernel
theorem fusedMap0360_checked : acceptsGraphIso
    (fused (graph core0360) (root 6) 0 3) DegreeOneSmallSpectrum381.graph fusedMap0360=true := by decide +kernel
theorem certified0360 : Certified (graph core0360) (root 6) 0 3 :=
  of_native_maps core0360 DegreeOneSmallSpectrum550.graph DegreeOneSmallSpectrum381.graph
    sourceMap0360 fusedMap0360 sourceMap0360_checked fusedMap0360_checked
    DegreeOneSmallComparisons.comparison0360
#print axioms sourceMap0360_checked
#print axioms fusedMap0360_checked
#print axioms certified0360
def sourceMap0360swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0360swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0360swap_checked : acceptsGraphIso
    (source (graph core0360) (root 6) 3 0) DegreeOneSmallSpectrum550.graph sourceMap0360swap=true := by decide +kernel
theorem fusedMap0360swap_checked : acceptsGraphIso
    (fused (graph core0360) (root 6) 3 0) DegreeOneSmallSpectrum381.graph fusedMap0360swap=true := by decide +kernel
theorem certified0360swap : Certified (graph core0360) (root 6) 3 0 :=
  of_native_maps core0360 DegreeOneSmallSpectrum550.graph DegreeOneSmallSpectrum381.graph
    sourceMap0360swap fusedMap0360swap sourceMap0360swap_checked fusedMap0360swap_checked
    DegreeOneSmallComparisons.comparison0360
#print axioms sourceMap0360swap_checked
#print axioms fusedMap0360swap_checked
#print axioms certified0360swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
