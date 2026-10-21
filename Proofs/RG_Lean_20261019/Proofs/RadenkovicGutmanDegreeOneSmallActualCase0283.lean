/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0283 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0283 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0283 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0283_checked : acceptsGraphIso
    (source (graph core0283) (root 6) 1 3) DegreeOneSmallSpectrum905.graph sourceMap0283=true := by decide +kernel
theorem fusedMap0283_checked : acceptsGraphIso
    (fused (graph core0283) (root 6) 1 3) DegreeOneSmallSpectrum856.graph fusedMap0283=true := by decide +kernel
theorem certified0283 : Certified (graph core0283) (root 6) 1 3 :=
  of_native_maps core0283 DegreeOneSmallSpectrum905.graph DegreeOneSmallSpectrum856.graph
    sourceMap0283 fusedMap0283 sourceMap0283_checked fusedMap0283_checked
    DegreeOneSmallComparisons.comparison0283
#print axioms sourceMap0283_checked
#print axioms fusedMap0283_checked
#print axioms certified0283
def sourceMap0283swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0283swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0283swap_checked : acceptsGraphIso
    (source (graph core0283) (root 6) 3 1) DegreeOneSmallSpectrum905.graph sourceMap0283swap=true := by decide +kernel
theorem fusedMap0283swap_checked : acceptsGraphIso
    (fused (graph core0283) (root 6) 3 1) DegreeOneSmallSpectrum856.graph fusedMap0283swap=true := by decide +kernel
theorem certified0283swap : Certified (graph core0283) (root 6) 3 1 :=
  of_native_maps core0283 DegreeOneSmallSpectrum905.graph DegreeOneSmallSpectrum856.graph
    sourceMap0283swap fusedMap0283swap sourceMap0283swap_checked fusedMap0283swap_checked
    DegreeOneSmallComparisons.comparison0283
#print axioms sourceMap0283swap_checked
#print axioms fusedMap0283swap_checked
#print axioms certified0283swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
