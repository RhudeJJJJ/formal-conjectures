/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1231 : Family 9 := level9.get ⟨20,by decide⟩
def sourceMap1231 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1231 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1231_checked : acceptsGraphIso
    (source (graph core1231) (root 9) 0 0) DegreeOneSmallSpectrum475.graph sourceMap1231=true := by decide +kernel
theorem fusedMap1231_checked : acceptsGraphIso
    (fused (graph core1231) (root 9) 0 0) DegreeOneSmallSpectrum385.graph fusedMap1231=true := by decide +kernel
theorem certified1231 : Certified (graph core1231) (root 9) 0 0 :=
  of_native_maps core1231 DegreeOneSmallSpectrum475.graph DegreeOneSmallSpectrum385.graph
    sourceMap1231 fusedMap1231 sourceMap1231_checked fusedMap1231_checked
    DegreeOneSmallComparisons.comparison1231
#print axioms sourceMap1231_checked
#print axioms fusedMap1231_checked
#print axioms certified1231
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
