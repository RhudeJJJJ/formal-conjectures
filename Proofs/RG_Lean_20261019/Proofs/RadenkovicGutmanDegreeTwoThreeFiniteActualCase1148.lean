/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1148 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap1148 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1148 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1148_checked : acceptsGraphIso
    (source (graph core1148) (root 8) 0 2) DegreeOneSmallSpectrum1483.graph sourceMap1148=true := by decide +kernel
theorem fusedMap1148_checked : acceptsGraphIso
    (fused (graph core1148) (root 8) 0 2) DegreeOneSmallSpectrum1485.graph fusedMap1148=true := by decide +kernel
theorem certified1148 : Certified (graph core1148) (root 8) 0 2 :=
  of_native_maps core1148 DegreeOneSmallSpectrum1483.graph DegreeOneSmallSpectrum1485.graph
    sourceMap1148 fusedMap1148 sourceMap1148_checked fusedMap1148_checked
    DegreeTwoThreeFiniteComparisons.comparison1148
#print axioms sourceMap1148_checked
#print axioms fusedMap1148_checked
#print axioms certified1148
def sourceMap1148swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1148swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1148swap_checked : acceptsGraphIso
    (source (graph core1148) (root 8) 2 0) DegreeOneSmallSpectrum1483.graph sourceMap1148swap=true := by decide +kernel
theorem fusedMap1148swap_checked : acceptsGraphIso
    (fused (graph core1148) (root 8) 2 0) DegreeOneSmallSpectrum1485.graph fusedMap1148swap=true := by decide +kernel
theorem certified1148swap : Certified (graph core1148) (root 8) 2 0 :=
  of_native_maps core1148 DegreeOneSmallSpectrum1483.graph DegreeOneSmallSpectrum1485.graph
    sourceMap1148swap fusedMap1148swap sourceMap1148swap_checked fusedMap1148swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1148
#print axioms sourceMap1148swap_checked
#print axioms fusedMap1148swap_checked
#print axioms certified1148swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
