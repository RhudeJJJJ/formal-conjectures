/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1004 : Family 10 := level10.get ⟨1725,by decide⟩
def sourceMap1004 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1004 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1004_checked : acceptsGraphIso
    (source (graph core1004) (root 10) 0 0) DegreeOneSmallSpectrum1921.graph sourceMap1004=true := by decide +kernel
theorem fusedMap1004_checked : acceptsGraphIso
    (fused (graph core1004) (root 10) 0 0) DegreeOneSmallSpectrum1920.graph fusedMap1004=true := by decide +kernel
theorem certified1004 : Certified (graph core1004) (root 10) 0 0 :=
  of_native_maps core1004 DegreeOneSmallSpectrum1921.graph DegreeOneSmallSpectrum1920.graph
    sourceMap1004 fusedMap1004 sourceMap1004_checked fusedMap1004_checked
    DegreeTwoThreeFiniteComparisons.comparison1004
#print axioms sourceMap1004_checked
#print axioms fusedMap1004_checked
#print axioms certified1004
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
