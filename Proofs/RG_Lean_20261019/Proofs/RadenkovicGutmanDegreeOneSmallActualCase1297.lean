/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1297 : Family 9 := level9.get ⟨64,by decide⟩
def sourceMap1297 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1297 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1297_checked : acceptsGraphIso
    (source (graph core1297) (root 9) 0 0) DegreeOneSmallSpectrum431.graph sourceMap1297=true := by decide +kernel
theorem fusedMap1297_checked : acceptsGraphIso
    (fused (graph core1297) (root 9) 0 0) DegreeOneSmallSpectrum494.graph fusedMap1297=true := by decide +kernel
theorem certified1297 : Certified (graph core1297) (root 9) 0 0 :=
  of_native_maps core1297 DegreeOneSmallSpectrum431.graph DegreeOneSmallSpectrum494.graph
    sourceMap1297 fusedMap1297 sourceMap1297_checked fusedMap1297_checked
    DegreeOneSmallComparisons.comparison1297
#print axioms sourceMap1297_checked
#print axioms fusedMap1297_checked
#print axioms certified1297
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
