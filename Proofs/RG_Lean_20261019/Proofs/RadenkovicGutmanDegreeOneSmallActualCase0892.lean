/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0892 : Family 8 := level8.get ⟨53,by decide⟩
def sourceMap0892 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0892 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0892_checked : acceptsGraphIso
    (source (graph core0892) (root 8) 0 1) DegreeOneSmallSpectrum503.graph sourceMap0892=true := by decide +kernel
theorem fusedMap0892_checked : acceptsGraphIso
    (fused (graph core0892) (root 8) 0 1) DegreeOneSmallSpectrum505.graph fusedMap0892=true := by decide +kernel
theorem certified0892 : Certified (graph core0892) (root 8) 0 1 :=
  of_native_maps core0892 DegreeOneSmallSpectrum503.graph DegreeOneSmallSpectrum505.graph
    sourceMap0892 fusedMap0892 sourceMap0892_checked fusedMap0892_checked
    DegreeOneSmallComparisons.comparison0892
#print axioms sourceMap0892_checked
#print axioms fusedMap0892_checked
#print axioms certified0892
def sourceMap0892swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0892swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0892swap_checked : acceptsGraphIso
    (source (graph core0892) (root 8) 1 0) DegreeOneSmallSpectrum503.graph sourceMap0892swap=true := by decide +kernel
theorem fusedMap0892swap_checked : acceptsGraphIso
    (fused (graph core0892) (root 8) 1 0) DegreeOneSmallSpectrum505.graph fusedMap0892swap=true := by decide +kernel
theorem certified0892swap : Certified (graph core0892) (root 8) 1 0 :=
  of_native_maps core0892 DegreeOneSmallSpectrum503.graph DegreeOneSmallSpectrum505.graph
    sourceMap0892swap fusedMap0892swap sourceMap0892swap_checked fusedMap0892swap_checked
    DegreeOneSmallComparisons.comparison0892
#print axioms sourceMap0892swap_checked
#print axioms fusedMap0892swap_checked
#print axioms certified0892swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
