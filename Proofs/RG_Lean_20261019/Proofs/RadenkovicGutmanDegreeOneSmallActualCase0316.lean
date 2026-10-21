/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0316 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0316 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0316 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0316_checked : acceptsGraphIso
    (source (graph core0316) (root 6) 0 4) DegreeOneSmallSpectrum865.graph sourceMap0316=true := by decide +kernel
theorem fusedMap0316_checked : acceptsGraphIso
    (fused (graph core0316) (root 6) 0 4) DegreeOneSmallSpectrum870.graph fusedMap0316=true := by decide +kernel
theorem certified0316 : Certified (graph core0316) (root 6) 0 4 :=
  of_native_maps core0316 DegreeOneSmallSpectrum865.graph DegreeOneSmallSpectrum870.graph
    sourceMap0316 fusedMap0316 sourceMap0316_checked fusedMap0316_checked
    DegreeOneSmallComparisons.comparison0316
#print axioms sourceMap0316_checked
#print axioms fusedMap0316_checked
#print axioms certified0316
def sourceMap0316swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0316swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0316swap_checked : acceptsGraphIso
    (source (graph core0316) (root 6) 4 0) DegreeOneSmallSpectrum865.graph sourceMap0316swap=true := by decide +kernel
theorem fusedMap0316swap_checked : acceptsGraphIso
    (fused (graph core0316) (root 6) 4 0) DegreeOneSmallSpectrum870.graph fusedMap0316swap=true := by decide +kernel
theorem certified0316swap : Certified (graph core0316) (root 6) 4 0 :=
  of_native_maps core0316 DegreeOneSmallSpectrum865.graph DegreeOneSmallSpectrum870.graph
    sourceMap0316swap fusedMap0316swap sourceMap0316swap_checked fusedMap0316swap_checked
    DegreeOneSmallComparisons.comparison0316
#print axioms sourceMap0316swap_checked
#print axioms fusedMap0316swap_checked
#print axioms certified0316swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
