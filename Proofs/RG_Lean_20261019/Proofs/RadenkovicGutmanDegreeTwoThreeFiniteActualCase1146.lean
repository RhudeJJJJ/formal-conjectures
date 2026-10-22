/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1146 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap1146 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1146 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1146_checked : acceptsGraphIso
    (source (graph core1146) (root 8) 0 2) DegreeOneSmallSpectrum1461.graph sourceMap1146=true := by decide +kernel
theorem fusedMap1146_checked : acceptsGraphIso
    (fused (graph core1146) (root 8) 0 2) DegreeOneSmallSpectrum1463.graph fusedMap1146=true := by decide +kernel
theorem certified1146 : Certified (graph core1146) (root 8) 0 2 :=
  of_native_maps core1146 DegreeOneSmallSpectrum1461.graph DegreeOneSmallSpectrum1463.graph
    sourceMap1146 fusedMap1146 sourceMap1146_checked fusedMap1146_checked
    DegreeTwoThreeFiniteComparisons.comparison1146
#print axioms sourceMap1146_checked
#print axioms fusedMap1146_checked
#print axioms certified1146
def sourceMap1146swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1146swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1146swap_checked : acceptsGraphIso
    (source (graph core1146) (root 8) 2 0) DegreeOneSmallSpectrum1461.graph sourceMap1146swap=true := by decide +kernel
theorem fusedMap1146swap_checked : acceptsGraphIso
    (fused (graph core1146) (root 8) 2 0) DegreeOneSmallSpectrum1463.graph fusedMap1146swap=true := by decide +kernel
theorem certified1146swap : Certified (graph core1146) (root 8) 2 0 :=
  of_native_maps core1146 DegreeOneSmallSpectrum1461.graph DegreeOneSmallSpectrum1463.graph
    sourceMap1146swap fusedMap1146swap sourceMap1146swap_checked fusedMap1146swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1146
#print axioms sourceMap1146swap_checked
#print axioms fusedMap1146swap_checked
#print axioms certified1146swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
