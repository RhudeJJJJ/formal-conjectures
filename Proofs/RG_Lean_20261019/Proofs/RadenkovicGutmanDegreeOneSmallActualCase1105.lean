/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1105 : Family 8 := level8.get ⟨151,by decide⟩
def sourceMap1105 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1105 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1105_checked : acceptsGraphIso
    (source (graph core1105) (root 8) 0 2) DegreeOneSmallSpectrum1407.graph sourceMap1105=true := by decide +kernel
theorem fusedMap1105_checked : acceptsGraphIso
    (fused (graph core1105) (root 8) 0 2) DegreeOneSmallSpectrum1408.graph fusedMap1105=true := by decide +kernel
theorem certified1105 : Certified (graph core1105) (root 8) 0 2 :=
  of_native_maps core1105 DegreeOneSmallSpectrum1407.graph DegreeOneSmallSpectrum1408.graph
    sourceMap1105 fusedMap1105 sourceMap1105_checked fusedMap1105_checked
    DegreeOneSmallComparisons.comparison1105
#print axioms sourceMap1105_checked
#print axioms fusedMap1105_checked
#print axioms certified1105
def sourceMap1105swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1105swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1105swap_checked : acceptsGraphIso
    (source (graph core1105) (root 8) 2 0) DegreeOneSmallSpectrum1407.graph sourceMap1105swap=true := by decide +kernel
theorem fusedMap1105swap_checked : acceptsGraphIso
    (fused (graph core1105) (root 8) 2 0) DegreeOneSmallSpectrum1408.graph fusedMap1105swap=true := by decide +kernel
theorem certified1105swap : Certified (graph core1105) (root 8) 2 0 :=
  of_native_maps core1105 DegreeOneSmallSpectrum1407.graph DegreeOneSmallSpectrum1408.graph
    sourceMap1105swap fusedMap1105swap sourceMap1105swap_checked fusedMap1105swap_checked
    DegreeOneSmallComparisons.comparison1105
#print axioms sourceMap1105swap_checked
#print axioms fusedMap1105swap_checked
#print axioms certified1105swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
