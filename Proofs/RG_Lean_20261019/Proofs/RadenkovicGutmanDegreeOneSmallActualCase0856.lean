/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0856 : Family 8 := level8.get ⟨39,by decide⟩
def sourceMap0856 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0856 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0856_checked : acceptsGraphIso
    (source (graph core0856) (root 8) 0 1) DegreeOneSmallSpectrum432.graph sourceMap0856=true := by decide +kernel
theorem fusedMap0856_checked : acceptsGraphIso
    (fused (graph core0856) (root 8) 0 1) DegreeOneSmallSpectrum434.graph fusedMap0856=true := by decide +kernel
theorem certified0856 : Certified (graph core0856) (root 8) 0 1 :=
  of_native_maps core0856 DegreeOneSmallSpectrum432.graph DegreeOneSmallSpectrum434.graph
    sourceMap0856 fusedMap0856 sourceMap0856_checked fusedMap0856_checked
    DegreeOneSmallComparisons.comparison0856
#print axioms sourceMap0856_checked
#print axioms fusedMap0856_checked
#print axioms certified0856
def sourceMap0856swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0856swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0856swap_checked : acceptsGraphIso
    (source (graph core0856) (root 8) 1 0) DegreeOneSmallSpectrum432.graph sourceMap0856swap=true := by decide +kernel
theorem fusedMap0856swap_checked : acceptsGraphIso
    (fused (graph core0856) (root 8) 1 0) DegreeOneSmallSpectrum434.graph fusedMap0856swap=true := by decide +kernel
theorem certified0856swap : Certified (graph core0856) (root 8) 1 0 :=
  of_native_maps core0856 DegreeOneSmallSpectrum432.graph DegreeOneSmallSpectrum434.graph
    sourceMap0856swap fusedMap0856swap sourceMap0856swap_checked fusedMap0856swap_checked
    DegreeOneSmallComparisons.comparison0856
#print axioms sourceMap0856swap_checked
#print axioms fusedMap0856swap_checked
#print axioms certified0856swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
