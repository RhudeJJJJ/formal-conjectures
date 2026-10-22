/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1003 : Family 10 := level10.get ⟨1724,by decide⟩
def sourceMap1003 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1003 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1003_checked : acceptsGraphIso
    (source (graph core1003) (root 10) 0 0) DegreeOneSmallSpectrum1916.graph sourceMap1003=true := by decide +kernel
theorem fusedMap1003_checked : acceptsGraphIso
    (fused (graph core1003) (root 10) 0 0) DegreeOneSmallSpectrum1915.graph fusedMap1003=true := by decide +kernel
theorem certified1003 : Certified (graph core1003) (root 10) 0 0 :=
  of_native_maps core1003 DegreeOneSmallSpectrum1916.graph DegreeOneSmallSpectrum1915.graph
    sourceMap1003 fusedMap1003 sourceMap1003_checked fusedMap1003_checked
    DegreeTwoThreeFiniteComparisons.comparison1003
#print axioms sourceMap1003_checked
#print axioms fusedMap1003_checked
#print axioms certified1003
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
