/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1453 : Family 9 := level9.get ⟨188,by decide⟩
def sourceMap1453 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1453 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1453_checked : acceptsGraphIso
    (source (graph core1453) (root 9) 0 0) DegreeOneSmallSpectrum679.graph sourceMap1453=true := by decide +kernel
theorem fusedMap1453_checked : acceptsGraphIso
    (fused (graph core1453) (root 9) 0 0) DegreeOneSmallSpectrum492.graph fusedMap1453=true := by decide +kernel
theorem certified1453 : Certified (graph core1453) (root 9) 0 0 :=
  of_native_maps core1453 DegreeOneSmallSpectrum679.graph DegreeOneSmallSpectrum492.graph
    sourceMap1453 fusedMap1453 sourceMap1453_checked fusedMap1453_checked
    DegreeOneSmallComparisons.comparison1453
#print axioms sourceMap1453_checked
#print axioms fusedMap1453_checked
#print axioms certified1453
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
