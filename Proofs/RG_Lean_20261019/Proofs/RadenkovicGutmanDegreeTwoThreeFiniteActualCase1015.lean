/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1015 : Family 10 := level10.get ⟨1785,by decide⟩
def sourceMap1015 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,10,11,12,1,2,3,4,5,6,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap1015 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,10,11,12,1,2,3,4,5,6,7,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1015_checked : acceptsGraphIso
    (source (graph core1015) (root 10) 0 0) DegreeOneSmallSpectrum1523.graph sourceMap1015=true := by decide +kernel
theorem fusedMap1015_checked : acceptsGraphIso
    (fused (graph core1015) (root 10) 0 0) DegreeOneSmallSpectrum1522.graph fusedMap1015=true := by decide +kernel
theorem certified1015 : Certified (graph core1015) (root 10) 0 0 :=
  of_native_maps core1015 DegreeOneSmallSpectrum1523.graph DegreeOneSmallSpectrum1522.graph
    sourceMap1015 fusedMap1015 sourceMap1015_checked fusedMap1015_checked
    DegreeTwoThreeFiniteComparisons.comparison1015
#print axioms sourceMap1015_checked
#print axioms fusedMap1015_checked
#print axioms certified1015
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
