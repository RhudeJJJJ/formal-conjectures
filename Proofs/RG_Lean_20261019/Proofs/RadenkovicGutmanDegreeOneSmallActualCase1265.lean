/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1265 : Family 9 := level9.get ⟨44,by decide⟩
def sourceMap1265 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1265 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1265_checked : acceptsGraphIso
    (source (graph core1265) (root 9) 0 0) DegreeOneSmallSpectrum408.graph sourceMap1265=true := by decide +kernel
theorem fusedMap1265_checked : acceptsGraphIso
    (fused (graph core1265) (root 9) 0 0) DegreeOneSmallSpectrum411.graph fusedMap1265=true := by decide +kernel
theorem certified1265 : Certified (graph core1265) (root 9) 0 0 :=
  of_native_maps core1265 DegreeOneSmallSpectrum408.graph DegreeOneSmallSpectrum411.graph
    sourceMap1265 fusedMap1265 sourceMap1265_checked fusedMap1265_checked
    DegreeOneSmallComparisons.comparison1265
#print axioms sourceMap1265_checked
#print axioms fusedMap1265_checked
#print axioms certified1265
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
