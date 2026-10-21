/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1243 : Family 9 := level9.get ⟨27,by decide⟩
def sourceMap1243 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1243 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1243_checked : acceptsGraphIso
    (source (graph core1243) (root 9) 0 0) DegreeOneSmallSpectrum456.graph sourceMap1243=true := by decide +kernel
theorem fusedMap1243_checked : acceptsGraphIso
    (fused (graph core1243) (root 9) 0 0) DegreeOneSmallSpectrum390.graph fusedMap1243=true := by decide +kernel
theorem certified1243 : Certified (graph core1243) (root 9) 0 0 :=
  of_native_maps core1243 DegreeOneSmallSpectrum456.graph DegreeOneSmallSpectrum390.graph
    sourceMap1243 fusedMap1243 sourceMap1243_checked fusedMap1243_checked
    DegreeOneSmallComparisons.comparison1243
#print axioms sourceMap1243_checked
#print axioms fusedMap1243_checked
#print axioms certified1243
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
