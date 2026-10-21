/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1012 : Family 8 := level8.get ⟨104,by decide⟩
def sourceMap1012 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1012 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1012_checked : acceptsGraphIso
    (source (graph core1012) (root 8) 0 1) DegreeOneSmallSpectrum668.graph sourceMap1012=true := by decide +kernel
theorem fusedMap1012_checked : acceptsGraphIso
    (fused (graph core1012) (root 8) 0 1) DegreeOneSmallSpectrum413.graph fusedMap1012=true := by decide +kernel
theorem certified1012 : Certified (graph core1012) (root 8) 0 1 :=
  of_native_maps core1012 DegreeOneSmallSpectrum668.graph DegreeOneSmallSpectrum413.graph
    sourceMap1012 fusedMap1012 sourceMap1012_checked fusedMap1012_checked
    DegreeOneSmallComparisons.comparison1012
#print axioms sourceMap1012_checked
#print axioms fusedMap1012_checked
#print axioms certified1012
def sourceMap1012swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1012swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1012swap_checked : acceptsGraphIso
    (source (graph core1012) (root 8) 1 0) DegreeOneSmallSpectrum668.graph sourceMap1012swap=true := by decide +kernel
theorem fusedMap1012swap_checked : acceptsGraphIso
    (fused (graph core1012) (root 8) 1 0) DegreeOneSmallSpectrum413.graph fusedMap1012swap=true := by decide +kernel
theorem certified1012swap : Certified (graph core1012) (root 8) 1 0 :=
  of_native_maps core1012 DegreeOneSmallSpectrum668.graph DegreeOneSmallSpectrum413.graph
    sourceMap1012swap fusedMap1012swap sourceMap1012swap_checked fusedMap1012swap_checked
    DegreeOneSmallComparisons.comparison1012
#print axioms sourceMap1012swap_checked
#print axioms fusedMap1012swap_checked
#print axioms certified1012swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
