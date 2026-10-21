/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1036 : Family 8 := level8.get ⟨115,by decide⟩
def sourceMap1036 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1036 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1036_checked : acceptsGraphIso
    (source (graph core1036) (root 8) 0 1) DegreeOneSmallSpectrum739.graph sourceMap1036=true := by decide +kernel
theorem fusedMap1036_checked : acceptsGraphIso
    (fused (graph core1036) (root 8) 0 1) DegreeOneSmallSpectrum441.graph fusedMap1036=true := by decide +kernel
theorem certified1036 : Certified (graph core1036) (root 8) 0 1 :=
  of_native_maps core1036 DegreeOneSmallSpectrum739.graph DegreeOneSmallSpectrum441.graph
    sourceMap1036 fusedMap1036 sourceMap1036_checked fusedMap1036_checked
    DegreeOneSmallComparisons.comparison1036
#print axioms sourceMap1036_checked
#print axioms fusedMap1036_checked
#print axioms certified1036
def sourceMap1036swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1036swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1036swap_checked : acceptsGraphIso
    (source (graph core1036) (root 8) 1 0) DegreeOneSmallSpectrum739.graph sourceMap1036swap=true := by decide +kernel
theorem fusedMap1036swap_checked : acceptsGraphIso
    (fused (graph core1036) (root 8) 1 0) DegreeOneSmallSpectrum441.graph fusedMap1036swap=true := by decide +kernel
theorem certified1036swap : Certified (graph core1036) (root 8) 1 0 :=
  of_native_maps core1036 DegreeOneSmallSpectrum739.graph DegreeOneSmallSpectrum441.graph
    sourceMap1036swap fusedMap1036swap sourceMap1036swap_checked fusedMap1036swap_checked
    DegreeOneSmallComparisons.comparison1036
#print axioms sourceMap1036swap_checked
#print axioms fusedMap1036swap_checked
#print axioms certified1036swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
