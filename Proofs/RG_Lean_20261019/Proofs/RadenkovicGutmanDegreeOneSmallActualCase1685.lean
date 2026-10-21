/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1685 : Family 9 := level9.get ⟨447,by decide⟩
def sourceMap1685 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1685 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1685_checked : acceptsGraphIso
    (source (graph core1685) (root 9) 0 0) DegreeOneSmallSpectrum681.graph sourceMap1685=true := by decide +kernel
theorem fusedMap1685_checked : acceptsGraphIso
    (fused (graph core1685) (root 9) 0 0) DegreeOneSmallSpectrum809.graph fusedMap1685=true := by decide +kernel
theorem certified1685 : Certified (graph core1685) (root 9) 0 0 :=
  of_native_maps core1685 DegreeOneSmallSpectrum681.graph DegreeOneSmallSpectrum809.graph
    sourceMap1685 fusedMap1685 sourceMap1685_checked fusedMap1685_checked
    DegreeOneSmallComparisons.comparison1685
#print axioms sourceMap1685_checked
#print axioms fusedMap1685_checked
#print axioms certified1685
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
