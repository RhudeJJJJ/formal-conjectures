/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1235 : Family 9 := level9.get ⟨23,by decide⟩
def sourceMap1235 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1235 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1235_checked : acceptsGraphIso
    (source (graph core1235) (root 9) 0 0) DegreeOneSmallSpectrum494.graph sourceMap1235=true := by decide +kernel
theorem fusedMap1235_checked : acceptsGraphIso
    (fused (graph core1235) (root 9) 0 0) DegreeOneSmallSpectrum387.graph fusedMap1235=true := by decide +kernel
theorem certified1235 : Certified (graph core1235) (root 9) 0 0 :=
  of_native_maps core1235 DegreeOneSmallSpectrum494.graph DegreeOneSmallSpectrum387.graph
    sourceMap1235 fusedMap1235 sourceMap1235_checked fusedMap1235_checked
    DegreeOneSmallComparisons.comparison1235
#print axioms sourceMap1235_checked
#print axioms fusedMap1235_checked
#print axioms certified1235
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
