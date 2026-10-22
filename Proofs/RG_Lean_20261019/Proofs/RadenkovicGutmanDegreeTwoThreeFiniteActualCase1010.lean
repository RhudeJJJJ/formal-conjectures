/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1010 : Family 10 := level10.get ⟨1744,by decide⟩
def sourceMap1010 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1010 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1010_checked : acceptsGraphIso
    (source (graph core1010) (root 10) 0 0) DegreeOneSmallSpectrum1941.graph sourceMap1010=true := by decide +kernel
theorem fusedMap1010_checked : acceptsGraphIso
    (fused (graph core1010) (root 10) 0 0) DegreeOneSmallSpectrum1940.graph fusedMap1010=true := by decide +kernel
theorem certified1010 : Certified (graph core1010) (root 10) 0 0 :=
  of_native_maps core1010 DegreeOneSmallSpectrum1941.graph DegreeOneSmallSpectrum1940.graph
    sourceMap1010 fusedMap1010 sourceMap1010_checked fusedMap1010_checked
    DegreeTwoThreeFiniteComparisons.comparison1010
#print axioms sourceMap1010_checked
#print axioms fusedMap1010_checked
#print axioms certified1010
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
