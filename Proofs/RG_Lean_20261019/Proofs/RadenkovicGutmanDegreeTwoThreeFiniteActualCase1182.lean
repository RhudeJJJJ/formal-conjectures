/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1182 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap1182 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1182 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1182_checked : acceptsGraphIso
    (source (graph core1182) (root 8) 0 2) DegreeOneSmallSpectrum1944.graph sourceMap1182=true := by decide +kernel
theorem fusedMap1182_checked : acceptsGraphIso
    (fused (graph core1182) (root 8) 0 2) DegreeOneSmallSpectrum1354.graph fusedMap1182=true := by decide +kernel
theorem certified1182 : Certified (graph core1182) (root 8) 0 2 :=
  of_native_maps core1182 DegreeOneSmallSpectrum1944.graph DegreeOneSmallSpectrum1354.graph
    sourceMap1182 fusedMap1182 sourceMap1182_checked fusedMap1182_checked
    DegreeTwoThreeFiniteComparisons.comparison1182
#print axioms sourceMap1182_checked
#print axioms fusedMap1182_checked
#print axioms certified1182
def sourceMap1182swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1182swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1182swap_checked : acceptsGraphIso
    (source (graph core1182) (root 8) 2 0) DegreeOneSmallSpectrum1944.graph sourceMap1182swap=true := by decide +kernel
theorem fusedMap1182swap_checked : acceptsGraphIso
    (fused (graph core1182) (root 8) 2 0) DegreeOneSmallSpectrum1354.graph fusedMap1182swap=true := by decide +kernel
theorem certified1182swap : Certified (graph core1182) (root 8) 2 0 :=
  of_native_maps core1182 DegreeOneSmallSpectrum1944.graph DegreeOneSmallSpectrum1354.graph
    sourceMap1182swap fusedMap1182swap sourceMap1182swap_checked fusedMap1182swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1182
#print axioms sourceMap1182swap_checked
#print axioms fusedMap1182swap_checked
#print axioms certified1182swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
