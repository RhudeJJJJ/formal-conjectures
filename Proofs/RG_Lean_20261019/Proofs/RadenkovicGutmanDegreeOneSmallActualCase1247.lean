/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1247 : Family 9 := level9.get ⟨30,by decide⟩
def sourceMap1247 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1247 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1247_checked : acceptsGraphIso
    (source (graph core1247) (root 9) 0 0) DegreeOneSmallSpectrum499.graph sourceMap1247=true := by decide +kernel
theorem fusedMap1247_checked : acceptsGraphIso
    (fused (graph core1247) (root 9) 0 0) DegreeOneSmallSpectrum394.graph fusedMap1247=true := by decide +kernel
theorem certified1247 : Certified (graph core1247) (root 9) 0 0 :=
  of_native_maps core1247 DegreeOneSmallSpectrum499.graph DegreeOneSmallSpectrum394.graph
    sourceMap1247 fusedMap1247 sourceMap1247_checked fusedMap1247_checked
    DegreeOneSmallComparisons.comparison1247
#print axioms sourceMap1247_checked
#print axioms fusedMap1247_checked
#print axioms certified1247
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
