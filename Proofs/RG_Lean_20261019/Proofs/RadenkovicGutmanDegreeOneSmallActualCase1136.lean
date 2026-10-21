/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1136 : Family 8 := level8.get ⟨188,by decide⟩
def sourceMap1136 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1136 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1136_checked : acceptsGraphIso
    (source (graph core1136) (root 8) 0 1) SmallGeFourSpectrum115.graph sourceMap1136=true := by decide +kernel
theorem fusedMap1136_checked : acceptsGraphIso
    (fused (graph core1136) (root 8) 0 1) SmallGeFourSpectrum116.graph fusedMap1136=true := by decide +kernel
theorem certified1136 : Certified (graph core1136) (root 8) 0 1 :=
  of_native_maps core1136 SmallGeFourSpectrum115.graph SmallGeFourSpectrum116.graph
    sourceMap1136 fusedMap1136 sourceMap1136_checked fusedMap1136_checked
    DegreeOneSmallComparisons.comparison1136
#print axioms sourceMap1136_checked
#print axioms fusedMap1136_checked
#print axioms certified1136
def sourceMap1136swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1136swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1136swap_checked : acceptsGraphIso
    (source (graph core1136) (root 8) 1 0) SmallGeFourSpectrum115.graph sourceMap1136swap=true := by decide +kernel
theorem fusedMap1136swap_checked : acceptsGraphIso
    (fused (graph core1136) (root 8) 1 0) SmallGeFourSpectrum116.graph fusedMap1136swap=true := by decide +kernel
theorem certified1136swap : Certified (graph core1136) (root 8) 1 0 :=
  of_native_maps core1136 SmallGeFourSpectrum115.graph SmallGeFourSpectrum116.graph
    sourceMap1136swap fusedMap1136swap sourceMap1136swap_checked fusedMap1136swap_checked
    DegreeOneSmallComparisons.comparison1136
#print axioms sourceMap1136swap_checked
#print axioms fusedMap1136swap_checked
#print axioms certified1136swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
