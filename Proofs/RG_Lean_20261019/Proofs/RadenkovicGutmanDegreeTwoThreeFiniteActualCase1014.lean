/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1014 : Family 10 := level10.get ⟨1768,by decide⟩
def sourceMap1014 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap1014 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,9,10,11,12,1,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap1014_checked : acceptsGraphIso
    (source (graph core1014) (root 10) 0 0) DegreeOneSmallSpectrum1539.graph sourceMap1014=true := by decide +kernel
theorem fusedMap1014_checked : acceptsGraphIso
    (fused (graph core1014) (root 10) 0 0) DegreeOneSmallSpectrum1535.graph fusedMap1014=true := by decide +kernel
theorem certified1014 : Certified (graph core1014) (root 10) 0 0 :=
  of_native_maps core1014 DegreeOneSmallSpectrum1539.graph DegreeOneSmallSpectrum1535.graph
    sourceMap1014 fusedMap1014 sourceMap1014_checked fusedMap1014_checked
    DegreeTwoThreeFiniteComparisons.comparison1014
#print axioms sourceMap1014_checked
#print axioms fusedMap1014_checked
#print axioms certified1014
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
