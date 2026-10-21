/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0013 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0013 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,4,2,3,0,5,6,7,8] (sourceLabel 1 1 4 v)
def fusedMap0013 : (Vertices 1 ⊕ Fin 7) → Fin 9 :=
  fun v => ![3,4,2,1,0,5,6,7,8] (fusedLabel 1 1 4 v)
theorem sourceMap0013_checked : acceptsGraphIso
    (source (graph core0013) (root 1) 1 4) DegreeOneSmallSpectrum035.graph sourceMap0013=true := by decide +kernel
theorem fusedMap0013_checked : acceptsGraphIso
    (fused (graph core0013) (root 1) 1 4) DegreeOneSmallSpectrum037.graph fusedMap0013=true := by decide +kernel
theorem certified0013 : Certified (graph core0013) (root 1) 1 4 :=
  of_native_maps core0013 DegreeOneSmallSpectrum035.graph DegreeOneSmallSpectrum037.graph
    sourceMap0013 fusedMap0013 sourceMap0013_checked fusedMap0013_checked
    DegreeOneSmallComparisons.comparison0013
#print axioms sourceMap0013_checked
#print axioms fusedMap0013_checked
#print axioms certified0013
def sourceMap0013swap : (Vertices 1 ⊕ Fin 5 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,4,0,5,6,7,8,2,3] (sourceLabel 1 4 1 v)
def fusedMap0013swap : (Vertices 1 ⊕ Fin 7) → Fin 9 :=
  fun v => ![3,4,2,1,0,5,6,7,8] (fusedLabel 1 4 1 v)
theorem sourceMap0013swap_checked : acceptsGraphIso
    (source (graph core0013) (root 1) 4 1) DegreeOneSmallSpectrum035.graph sourceMap0013swap=true := by decide +kernel
theorem fusedMap0013swap_checked : acceptsGraphIso
    (fused (graph core0013) (root 1) 4 1) DegreeOneSmallSpectrum037.graph fusedMap0013swap=true := by decide +kernel
theorem certified0013swap : Certified (graph core0013) (root 1) 4 1 :=
  of_native_maps core0013 DegreeOneSmallSpectrum035.graph DegreeOneSmallSpectrum037.graph
    sourceMap0013swap fusedMap0013swap sourceMap0013swap_checked fusedMap0013swap_checked
    DegreeOneSmallComparisons.comparison0013
#print axioms sourceMap0013swap_checked
#print axioms fusedMap0013swap_checked
#print axioms certified0013swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
