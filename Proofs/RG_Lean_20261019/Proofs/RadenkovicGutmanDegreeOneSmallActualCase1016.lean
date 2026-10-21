/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1016 : Family 8 := level8.get ⟨108,by decide⟩
def sourceMap1016 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1016 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1016_checked : acceptsGraphIso
    (source (graph core1016) (root 8) 0 1) DegreeOneSmallSpectrum682.graph sourceMap1016=true := by decide +kernel
theorem fusedMap1016_checked : acceptsGraphIso
    (fused (graph core1016) (root 8) 0 1) DegreeOneSmallSpectrum428.graph fusedMap1016=true := by decide +kernel
theorem certified1016 : Certified (graph core1016) (root 8) 0 1 :=
  of_native_maps core1016 DegreeOneSmallSpectrum682.graph DegreeOneSmallSpectrum428.graph
    sourceMap1016 fusedMap1016 sourceMap1016_checked fusedMap1016_checked
    DegreeOneSmallComparisons.comparison1016
#print axioms sourceMap1016_checked
#print axioms fusedMap1016_checked
#print axioms certified1016
def sourceMap1016swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1016swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1016swap_checked : acceptsGraphIso
    (source (graph core1016) (root 8) 1 0) DegreeOneSmallSpectrum682.graph sourceMap1016swap=true := by decide +kernel
theorem fusedMap1016swap_checked : acceptsGraphIso
    (fused (graph core1016) (root 8) 1 0) DegreeOneSmallSpectrum428.graph fusedMap1016swap=true := by decide +kernel
theorem certified1016swap : Certified (graph core1016) (root 8) 1 0 :=
  of_native_maps core1016 DegreeOneSmallSpectrum682.graph DegreeOneSmallSpectrum428.graph
    sourceMap1016swap fusedMap1016swap sourceMap1016swap_checked fusedMap1016swap_checked
    DegreeOneSmallComparisons.comparison1016
#print axioms sourceMap1016swap_checked
#print axioms fusedMap1016swap_checked
#print axioms certified1016swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
