/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1138 : Family 8 := level8.get ⟨188,by decide⟩
def sourceMap1138 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1138 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1138_checked : acceptsGraphIso
    (source (graph core1138) (root 8) 1 1) DegreeOneSmallSpectrum1529.graph sourceMap1138=true := by decide +kernel
theorem fusedMap1138_checked : acceptsGraphIso
    (fused (graph core1138) (root 8) 1 1) DegreeOneSmallSpectrum979.graph fusedMap1138=true := by decide +kernel
theorem certified1138 : Certified (graph core1138) (root 8) 1 1 :=
  of_native_maps core1138 DegreeOneSmallSpectrum1529.graph DegreeOneSmallSpectrum979.graph
    sourceMap1138 fusedMap1138 sourceMap1138_checked fusedMap1138_checked
    DegreeOneSmallComparisons.comparison1138
#print axioms sourceMap1138_checked
#print axioms fusedMap1138_checked
#print axioms certified1138
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
