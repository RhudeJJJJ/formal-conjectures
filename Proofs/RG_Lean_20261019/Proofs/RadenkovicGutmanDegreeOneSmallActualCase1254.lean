/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1254 : Family 9 := level9.get ⟨34,by decide⟩
def sourceMap1254 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1254 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1254_checked : acceptsGraphIso
    (source (graph core1254) (root 9) 0 1) DegreeOneSmallSpectrum930.graph sourceMap1254=true := by decide +kernel
theorem fusedMap1254_checked : acceptsGraphIso
    (fused (graph core1254) (root 9) 0 1) DegreeOneSmallSpectrum977.graph fusedMap1254=true := by decide +kernel
theorem certified1254 : Certified (graph core1254) (root 9) 0 1 :=
  of_native_maps core1254 DegreeOneSmallSpectrum930.graph DegreeOneSmallSpectrum977.graph
    sourceMap1254 fusedMap1254 sourceMap1254_checked fusedMap1254_checked
    DegreeOneSmallComparisons.comparison1254
#print axioms sourceMap1254_checked
#print axioms fusedMap1254_checked
#print axioms certified1254
def sourceMap1254swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1254swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1254swap_checked : acceptsGraphIso
    (source (graph core1254) (root 9) 1 0) DegreeOneSmallSpectrum930.graph sourceMap1254swap=true := by decide +kernel
theorem fusedMap1254swap_checked : acceptsGraphIso
    (fused (graph core1254) (root 9) 1 0) DegreeOneSmallSpectrum977.graph fusedMap1254swap=true := by decide +kernel
theorem certified1254swap : Certified (graph core1254) (root 9) 1 0 :=
  of_native_maps core1254 DegreeOneSmallSpectrum930.graph DegreeOneSmallSpectrum977.graph
    sourceMap1254swap fusedMap1254swap sourceMap1254swap_checked fusedMap1254swap_checked
    DegreeOneSmallComparisons.comparison1254
#print axioms sourceMap1254swap_checked
#print axioms fusedMap1254swap_checked
#print axioms certified1254swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
