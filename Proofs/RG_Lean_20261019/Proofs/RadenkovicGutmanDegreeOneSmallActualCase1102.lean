/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1102 : Family 8 := level8.get ⟨150,by decide⟩
def sourceMap1102 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1102 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1102_checked : acceptsGraphIso
    (source (graph core1102) (root 8) 1 1) DegreeOneSmallSpectrum1923.graph sourceMap1102=true := by decide +kernel
theorem fusedMap1102_checked : acceptsGraphIso
    (fused (graph core1102) (root 8) 1 1) DegreeOneSmallSpectrum1403.graph fusedMap1102=true := by decide +kernel
theorem certified1102 : Certified (graph core1102) (root 8) 1 1 :=
  of_native_maps core1102 DegreeOneSmallSpectrum1923.graph DegreeOneSmallSpectrum1403.graph
    sourceMap1102 fusedMap1102 sourceMap1102_checked fusedMap1102_checked
    DegreeOneSmallComparisons.comparison1102
#print axioms sourceMap1102_checked
#print axioms fusedMap1102_checked
#print axioms certified1102
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
