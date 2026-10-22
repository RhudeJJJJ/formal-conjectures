/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1144 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap1144 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1144 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 0 2 v)
theorem sourceMap1144_checked : acceptsGraphIso
    (source (graph core1144) (root 8) 0 2) DegreeOneSmallSpectrum1438.graph sourceMap1144=true := by decide +kernel
theorem fusedMap1144_checked : acceptsGraphIso
    (fused (graph core1144) (root 8) 0 2) DegreeOneSmallSpectrum1452.graph fusedMap1144=true := by decide +kernel
theorem certified1144 : Certified (graph core1144) (root 8) 0 2 :=
  of_native_maps core1144 DegreeOneSmallSpectrum1438.graph DegreeOneSmallSpectrum1452.graph
    sourceMap1144 fusedMap1144 sourceMap1144_checked fusedMap1144_checked
    DegreeTwoThreeFiniteComparisons.comparison1144
#print axioms sourceMap1144_checked
#print axioms fusedMap1144_checked
#print axioms certified1144
def sourceMap1144swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1144swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 2 0 v)
theorem sourceMap1144swap_checked : acceptsGraphIso
    (source (graph core1144) (root 8) 2 0) DegreeOneSmallSpectrum1438.graph sourceMap1144swap=true := by decide +kernel
theorem fusedMap1144swap_checked : acceptsGraphIso
    (fused (graph core1144) (root 8) 2 0) DegreeOneSmallSpectrum1452.graph fusedMap1144swap=true := by decide +kernel
theorem certified1144swap : Certified (graph core1144) (root 8) 2 0 :=
  of_native_maps core1144 DegreeOneSmallSpectrum1438.graph DegreeOneSmallSpectrum1452.graph
    sourceMap1144swap fusedMap1144swap sourceMap1144swap_checked fusedMap1144swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1144
#print axioms sourceMap1144swap_checked
#print axioms fusedMap1144swap_checked
#print axioms certified1144swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
