/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1183 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap1183 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1183 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1183_checked : acceptsGraphIso
    (source (graph core1183) (root 8) 0 2) DegreeOneSmallSpectrum1950.graph sourceMap1183=true := by decide +kernel
theorem fusedMap1183_checked : acceptsGraphIso
    (fused (graph core1183) (root 8) 0 2) DegreeOneSmallSpectrum1365.graph fusedMap1183=true := by decide +kernel
theorem certified1183 : Certified (graph core1183) (root 8) 0 2 :=
  of_native_maps core1183 DegreeOneSmallSpectrum1950.graph DegreeOneSmallSpectrum1365.graph
    sourceMap1183 fusedMap1183 sourceMap1183_checked fusedMap1183_checked
    DegreeTwoThreeFiniteComparisons.comparison1183
#print axioms sourceMap1183_checked
#print axioms fusedMap1183_checked
#print axioms certified1183
def sourceMap1183swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1183swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1183swap_checked : acceptsGraphIso
    (source (graph core1183) (root 8) 2 0) DegreeOneSmallSpectrum1950.graph sourceMap1183swap=true := by decide +kernel
theorem fusedMap1183swap_checked : acceptsGraphIso
    (fused (graph core1183) (root 8) 2 0) DegreeOneSmallSpectrum1365.graph fusedMap1183swap=true := by decide +kernel
theorem certified1183swap : Certified (graph core1183) (root 8) 2 0 :=
  of_native_maps core1183 DegreeOneSmallSpectrum1950.graph DegreeOneSmallSpectrum1365.graph
    sourceMap1183swap fusedMap1183swap sourceMap1183swap_checked fusedMap1183swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1183
#print axioms sourceMap1183swap_checked
#print axioms fusedMap1183swap_checked
#print axioms certified1183swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
