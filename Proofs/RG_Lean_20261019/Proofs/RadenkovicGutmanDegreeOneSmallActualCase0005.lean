/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0005 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0005 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (sourceLabel 1 0 5 v)
def fusedMap0005 : (Vertices 1 ⊕ Fin 7) → Fin 9 :=
  fun v => ![3,4,2,1,0,5,6,7,8] (fusedLabel 1 0 5 v)
theorem sourceMap0005_checked : acceptsGraphIso
    (source (graph core0005) (root 1) 0 5) DegreeOneSmallSpectrum034.graph sourceMap0005=true := by decide +kernel
theorem fusedMap0005_checked : acceptsGraphIso
    (fused (graph core0005) (root 1) 0 5) DegreeOneSmallSpectrum037.graph fusedMap0005=true := by decide +kernel
theorem certified0005 : Certified (graph core0005) (root 1) 0 5 :=
  of_native_maps core0005 DegreeOneSmallSpectrum034.graph DegreeOneSmallSpectrum037.graph
    sourceMap0005 fusedMap0005 sourceMap0005_checked fusedMap0005_checked
    DegreeOneSmallComparisons.comparison0005
#print axioms sourceMap0005_checked
#print axioms fusedMap0005_checked
#print axioms certified0005
def sourceMap0005swap : (Vertices 1 ⊕ Fin 6 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,3,1,0,5,6,7,8,4] (sourceLabel 1 5 0 v)
def fusedMap0005swap : (Vertices 1 ⊕ Fin 7) → Fin 9 :=
  fun v => ![3,4,2,1,0,5,6,7,8] (fusedLabel 1 5 0 v)
theorem sourceMap0005swap_checked : acceptsGraphIso
    (source (graph core0005) (root 1) 5 0) DegreeOneSmallSpectrum034.graph sourceMap0005swap=true := by decide +kernel
theorem fusedMap0005swap_checked : acceptsGraphIso
    (fused (graph core0005) (root 1) 5 0) DegreeOneSmallSpectrum037.graph fusedMap0005swap=true := by decide +kernel
theorem certified0005swap : Certified (graph core0005) (root 1) 5 0 :=
  of_native_maps core0005 DegreeOneSmallSpectrum034.graph DegreeOneSmallSpectrum037.graph
    sourceMap0005swap fusedMap0005swap sourceMap0005swap_checked fusedMap0005swap_checked
    DegreeOneSmallComparisons.comparison0005
#print axioms sourceMap0005swap_checked
#print axioms fusedMap0005swap_checked
#print axioms certified0005swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
