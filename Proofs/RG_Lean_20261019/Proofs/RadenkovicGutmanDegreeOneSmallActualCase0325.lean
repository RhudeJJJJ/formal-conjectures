/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0325 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0325 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0325 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0325_checked : acceptsGraphIso
    (source (graph core0325) (root 6) 0 4) DegreeOneSmallSpectrum874.graph sourceMap0325=true := by decide +kernel
theorem fusedMap0325_checked : acceptsGraphIso
    (fused (graph core0325) (root 6) 0 4) DegreeOneSmallSpectrum879.graph fusedMap0325=true := by decide +kernel
theorem certified0325 : Certified (graph core0325) (root 6) 0 4 :=
  of_native_maps core0325 DegreeOneSmallSpectrum874.graph DegreeOneSmallSpectrum879.graph
    sourceMap0325 fusedMap0325 sourceMap0325_checked fusedMap0325_checked
    DegreeOneSmallComparisons.comparison0325
#print axioms sourceMap0325_checked
#print axioms fusedMap0325_checked
#print axioms certified0325
def sourceMap0325swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0325swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0325swap_checked : acceptsGraphIso
    (source (graph core0325) (root 6) 4 0) DegreeOneSmallSpectrum874.graph sourceMap0325swap=true := by decide +kernel
theorem fusedMap0325swap_checked : acceptsGraphIso
    (fused (graph core0325) (root 6) 4 0) DegreeOneSmallSpectrum879.graph fusedMap0325swap=true := by decide +kernel
theorem certified0325swap : Certified (graph core0325) (root 6) 4 0 :=
  of_native_maps core0325 DegreeOneSmallSpectrum874.graph DegreeOneSmallSpectrum879.graph
    sourceMap0325swap fusedMap0325swap sourceMap0325swap_checked fusedMap0325swap_checked
    DegreeOneSmallComparisons.comparison0325
#print axioms sourceMap0325swap_checked
#print axioms fusedMap0325swap_checked
#print axioms certified0325swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
