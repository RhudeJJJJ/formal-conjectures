/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1008 : Family 10 := level10.get ⟨1740,by decide⟩
def sourceMap1008 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1008 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1008_checked : acceptsGraphIso
    (source (graph core1008) (root 10) 0 0) DegreeOneSmallSpectrum1939.graph sourceMap1008=true := by decide +kernel
theorem fusedMap1008_checked : acceptsGraphIso
    (fused (graph core1008) (root 10) 0 0) DegreeOneSmallSpectrum1938.graph fusedMap1008=true := by decide +kernel
theorem certified1008 : Certified (graph core1008) (root 10) 0 0 :=
  of_native_maps core1008 DegreeOneSmallSpectrum1939.graph DegreeOneSmallSpectrum1938.graph
    sourceMap1008 fusedMap1008 sourceMap1008_checked fusedMap1008_checked
    DegreeTwoThreeFiniteComparisons.comparison1008
#print axioms sourceMap1008_checked
#print axioms fusedMap1008_checked
#print axioms certified1008
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
