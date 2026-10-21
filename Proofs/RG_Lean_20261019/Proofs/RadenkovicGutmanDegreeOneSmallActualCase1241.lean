/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1241 : Family 9 := level9.get ⟨26,by decide⟩
def sourceMap1241 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1241 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1241_checked : acceptsGraphIso
    (source (graph core1241) (root 9) 0 0) DegreeOneSmallSpectrum478.graph sourceMap1241=true := by decide +kernel
theorem fusedMap1241_checked : acceptsGraphIso
    (fused (graph core1241) (root 9) 0 0) DegreeOneSmallSpectrum391.graph fusedMap1241=true := by decide +kernel
theorem certified1241 : Certified (graph core1241) (root 9) 0 0 :=
  of_native_maps core1241 DegreeOneSmallSpectrum478.graph DegreeOneSmallSpectrum391.graph
    sourceMap1241 fusedMap1241 sourceMap1241_checked fusedMap1241_checked
    DegreeOneSmallComparisons.comparison1241
#print axioms sourceMap1241_checked
#print axioms fusedMap1241_checked
#print axioms certified1241
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
