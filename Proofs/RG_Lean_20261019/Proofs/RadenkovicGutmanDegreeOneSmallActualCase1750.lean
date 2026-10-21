/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1750 : Family 9 := level9.get ⟨586,by decide⟩
def sourceMap1750 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1750 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1750_checked : acceptsGraphIso
    (source (graph core1750) (root 9) 0 1) DegreeOneSmallSpectrum1704.graph sourceMap1750=true := by decide +kernel
theorem fusedMap1750_checked : acceptsGraphIso
    (fused (graph core1750) (root 9) 0 1) DegreeOneSmallSpectrum1705.graph fusedMap1750=true := by decide +kernel
theorem certified1750 : Certified (graph core1750) (root 9) 0 1 :=
  of_native_maps core1750 DegreeOneSmallSpectrum1704.graph DegreeOneSmallSpectrum1705.graph
    sourceMap1750 fusedMap1750 sourceMap1750_checked fusedMap1750_checked
    DegreeOneSmallComparisons.comparison1750
#print axioms sourceMap1750_checked
#print axioms fusedMap1750_checked
#print axioms certified1750
def sourceMap1750swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1750swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1750swap_checked : acceptsGraphIso
    (source (graph core1750) (root 9) 1 0) DegreeOneSmallSpectrum1704.graph sourceMap1750swap=true := by decide +kernel
theorem fusedMap1750swap_checked : acceptsGraphIso
    (fused (graph core1750) (root 9) 1 0) DegreeOneSmallSpectrum1705.graph fusedMap1750swap=true := by decide +kernel
theorem certified1750swap : Certified (graph core1750) (root 9) 1 0 :=
  of_native_maps core1750 DegreeOneSmallSpectrum1704.graph DegreeOneSmallSpectrum1705.graph
    sourceMap1750swap fusedMap1750swap sourceMap1750swap_checked fusedMap1750swap_checked
    DegreeOneSmallComparisons.comparison1750
#print axioms sourceMap1750swap_checked
#print axioms fusedMap1750swap_checked
#print axioms certified1750swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
