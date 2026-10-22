/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1175 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap1175 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,5,6,7] (sourceLabel 8 0 2 v)
def fusedMap1175 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1175_checked : acceptsGraphIso
    (source (graph core1175) (root 8) 0 2) DegreeOneSmallSpectrum1879.graph sourceMap1175=true := by decide +kernel
theorem fusedMap1175_checked : acceptsGraphIso
    (fused (graph core1175) (root 8) 0 2) DegreeOneSmallSpectrum1190.graph fusedMap1175=true := by decide +kernel
theorem certified1175 : Certified (graph core1175) (root 8) 0 2 :=
  of_native_maps core1175 DegreeOneSmallSpectrum1879.graph DegreeOneSmallSpectrum1190.graph
    sourceMap1175 fusedMap1175 sourceMap1175_checked fusedMap1175_checked
    DegreeTwoThreeFiniteComparisons.comparison1175
#print axioms sourceMap1175_checked
#print axioms fusedMap1175_checked
#print axioms certified1175
def sourceMap1175swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7,12] (sourceLabel 8 2 0 v)
def fusedMap1175swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1175swap_checked : acceptsGraphIso
    (source (graph core1175) (root 8) 2 0) DegreeOneSmallSpectrum1879.graph sourceMap1175swap=true := by decide +kernel
theorem fusedMap1175swap_checked : acceptsGraphIso
    (fused (graph core1175) (root 8) 2 0) DegreeOneSmallSpectrum1190.graph fusedMap1175swap=true := by decide +kernel
theorem certified1175swap : Certified (graph core1175) (root 8) 2 0 :=
  of_native_maps core1175 DegreeOneSmallSpectrum1879.graph DegreeOneSmallSpectrum1190.graph
    sourceMap1175swap fusedMap1175swap sourceMap1175swap_checked fusedMap1175swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1175
#print axioms sourceMap1175swap_checked
#print axioms fusedMap1175swap_checked
#print axioms certified1175swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
