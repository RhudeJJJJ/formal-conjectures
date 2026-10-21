/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1066 : Family 8 := level8.get ⟨133,by decide⟩
def sourceMap1066 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1066 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1066_checked : acceptsGraphIso
    (source (graph core1066) (root 8) 1 1) DegreeOneSmallSpectrum1904.graph sourceMap1066=true := by decide +kernel
theorem fusedMap1066_checked : acceptsGraphIso
    (fused (graph core1066) (root 8) 1 1) DegreeOneSmallSpectrum1301.graph fusedMap1066=true := by decide +kernel
theorem certified1066 : Certified (graph core1066) (root 8) 1 1 :=
  of_native_maps core1066 DegreeOneSmallSpectrum1904.graph DegreeOneSmallSpectrum1301.graph
    sourceMap1066 fusedMap1066 sourceMap1066_checked fusedMap1066_checked
    DegreeOneSmallComparisons.comparison1066
#print axioms sourceMap1066_checked
#print axioms fusedMap1066_checked
#print axioms certified1066
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
