/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1074 : Family 8 := level8.get ⟨136,by decide⟩
def sourceMap1074 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1074 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1074_checked : acceptsGraphIso
    (source (graph core1074) (root 8) 1 1) DegreeOneSmallSpectrum1915.graph sourceMap1074=true := by decide +kernel
theorem fusedMap1074_checked : acceptsGraphIso
    (fused (graph core1074) (root 8) 1 1) DegreeOneSmallSpectrum1319.graph fusedMap1074=true := by decide +kernel
theorem certified1074 : Certified (graph core1074) (root 8) 1 1 :=
  of_native_maps core1074 DegreeOneSmallSpectrum1915.graph DegreeOneSmallSpectrum1319.graph
    sourceMap1074 fusedMap1074 sourceMap1074_checked fusedMap1074_checked
    DegreeOneSmallComparisons.comparison1074
#print axioms sourceMap1074_checked
#print axioms fusedMap1074_checked
#print axioms certified1074
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
