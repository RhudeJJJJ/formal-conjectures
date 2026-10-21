/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1190 : Family 8 := level8.get ⟨240,by decide⟩
def sourceMap1190 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,5,6,7,8,9,10,11,12,1,2,3,4] (sourceLabel 8 1 1 v)
def fusedMap1190 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1190_checked : acceptsGraphIso
    (source (graph core1190) (root 8) 1 1) DegreeOneSmallSpectrum1917.graph sourceMap1190=true := by decide +kernel
theorem fusedMap1190_checked : acceptsGraphIso
    (fused (graph core1190) (root 8) 1 1) DegreeOneSmallSpectrum1349.graph fusedMap1190=true := by decide +kernel
theorem certified1190 : Certified (graph core1190) (root 8) 1 1 :=
  of_native_maps core1190 DegreeOneSmallSpectrum1917.graph DegreeOneSmallSpectrum1349.graph
    sourceMap1190 fusedMap1190 sourceMap1190_checked fusedMap1190_checked
    DegreeOneSmallComparisons.comparison1190
#print axioms sourceMap1190_checked
#print axioms fusedMap1190_checked
#print axioms certified1190
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
