/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1185 : Family 8 := level8.get ⟨248,by decide⟩
def sourceMap1185 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1185 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1185_checked : acceptsGraphIso
    (source (graph core1185) (root 8) 0 2) DegreeOneSmallSpectrum1957.graph sourceMap1185=true := by decide +kernel
theorem fusedMap1185_checked : acceptsGraphIso
    (fused (graph core1185) (root 8) 0 2) DegreeOneSmallSpectrum1394.graph fusedMap1185=true := by decide +kernel
theorem certified1185 : Certified (graph core1185) (root 8) 0 2 :=
  of_native_maps core1185 DegreeOneSmallSpectrum1957.graph DegreeOneSmallSpectrum1394.graph
    sourceMap1185 fusedMap1185 sourceMap1185_checked fusedMap1185_checked
    DegreeTwoThreeFiniteComparisons.comparison1185
#print axioms sourceMap1185_checked
#print axioms fusedMap1185_checked
#print axioms certified1185
def sourceMap1185swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1185swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1185swap_checked : acceptsGraphIso
    (source (graph core1185) (root 8) 2 0) DegreeOneSmallSpectrum1957.graph sourceMap1185swap=true := by decide +kernel
theorem fusedMap1185swap_checked : acceptsGraphIso
    (fused (graph core1185) (root 8) 2 0) DegreeOneSmallSpectrum1394.graph fusedMap1185swap=true := by decide +kernel
theorem certified1185swap : Certified (graph core1185) (root 8) 2 0 :=
  of_native_maps core1185 DegreeOneSmallSpectrum1957.graph DegreeOneSmallSpectrum1394.graph
    sourceMap1185swap fusedMap1185swap sourceMap1185swap_checked fusedMap1185swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1185
#print axioms sourceMap1185swap_checked
#print axioms fusedMap1185swap_checked
#print axioms certified1185swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
