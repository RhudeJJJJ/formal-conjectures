/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1212 : Family 9 := level9.get ⟨9,by decide⟩
def sourceMap1212 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1212 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1212_checked : acceptsGraphIso
    (source (graph core1212) (root 9) 0 1) DegreeOneSmallSpectrum867.graph sourceMap1212=true := by decide +kernel
theorem fusedMap1212_checked : acceptsGraphIso
    (fused (graph core1212) (root 9) 0 1) DegreeOneSmallSpectrum870.graph fusedMap1212=true := by decide +kernel
theorem certified1212 : Certified (graph core1212) (root 9) 0 1 :=
  of_native_maps core1212 DegreeOneSmallSpectrum867.graph DegreeOneSmallSpectrum870.graph
    sourceMap1212 fusedMap1212 sourceMap1212_checked fusedMap1212_checked
    DegreeOneSmallComparisons.comparison1212
#print axioms sourceMap1212_checked
#print axioms fusedMap1212_checked
#print axioms certified1212
def sourceMap1212swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1212swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1212swap_checked : acceptsGraphIso
    (source (graph core1212) (root 9) 1 0) DegreeOneSmallSpectrum867.graph sourceMap1212swap=true := by decide +kernel
theorem fusedMap1212swap_checked : acceptsGraphIso
    (fused (graph core1212) (root 9) 1 0) DegreeOneSmallSpectrum870.graph fusedMap1212swap=true := by decide +kernel
theorem certified1212swap : Certified (graph core1212) (root 9) 1 0 :=
  of_native_maps core1212 DegreeOneSmallSpectrum867.graph DegreeOneSmallSpectrum870.graph
    sourceMap1212swap fusedMap1212swap sourceMap1212swap_checked fusedMap1212swap_checked
    DegreeOneSmallComparisons.comparison1212
#print axioms sourceMap1212swap_checked
#print axioms fusedMap1212swap_checked
#print axioms certified1212swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
