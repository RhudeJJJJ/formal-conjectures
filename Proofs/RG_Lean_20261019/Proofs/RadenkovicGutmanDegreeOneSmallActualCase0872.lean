/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0872 : Family 8 := level8.get ⟨44,by decide⟩
def sourceMap0872 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0872 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0872_checked : acceptsGraphIso
    (source (graph core0872) (root 8) 0 1) DegreeOneSmallSpectrum462.graph sourceMap0872=true := by decide +kernel
theorem fusedMap0872_checked : acceptsGraphIso
    (fused (graph core0872) (root 8) 0 1) DegreeOneSmallSpectrum464.graph fusedMap0872=true := by decide +kernel
theorem certified0872 : Certified (graph core0872) (root 8) 0 1 :=
  of_native_maps core0872 DegreeOneSmallSpectrum462.graph DegreeOneSmallSpectrum464.graph
    sourceMap0872 fusedMap0872 sourceMap0872_checked fusedMap0872_checked
    DegreeOneSmallComparisons.comparison0872
#print axioms sourceMap0872_checked
#print axioms fusedMap0872_checked
#print axioms certified0872
def sourceMap0872swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0872swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0872swap_checked : acceptsGraphIso
    (source (graph core0872) (root 8) 1 0) DegreeOneSmallSpectrum462.graph sourceMap0872swap=true := by decide +kernel
theorem fusedMap0872swap_checked : acceptsGraphIso
    (fused (graph core0872) (root 8) 1 0) DegreeOneSmallSpectrum464.graph fusedMap0872swap=true := by decide +kernel
theorem certified0872swap : Certified (graph core0872) (root 8) 1 0 :=
  of_native_maps core0872 DegreeOneSmallSpectrum462.graph DegreeOneSmallSpectrum464.graph
    sourceMap0872swap fusedMap0872swap sourceMap0872swap_checked fusedMap0872swap_checked
    DegreeOneSmallComparisons.comparison0872
#print axioms sourceMap0872swap_checked
#print axioms fusedMap0872swap_checked
#print axioms certified0872swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
