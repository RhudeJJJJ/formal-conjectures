/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1005 : Family 10 := level10.get ⟨1729,by decide⟩
def sourceMap1005 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap1005 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap1005_checked : acceptsGraphIso
    (source (graph core1005) (root 10) 0 0) DegreeOneSmallSpectrum1575.graph sourceMap1005=true := by decide +kernel
theorem fusedMap1005_checked : acceptsGraphIso
    (fused (graph core1005) (root 10) 0 0) DegreeOneSmallSpectrum1566.graph fusedMap1005=true := by decide +kernel
theorem certified1005 : Certified (graph core1005) (root 10) 0 0 :=
  of_native_maps core1005 DegreeOneSmallSpectrum1575.graph DegreeOneSmallSpectrum1566.graph
    sourceMap1005 fusedMap1005 sourceMap1005_checked fusedMap1005_checked
    DegreeTwoThreeFiniteComparisons.comparison1005
#print axioms sourceMap1005_checked
#print axioms fusedMap1005_checked
#print axioms certified1005
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
