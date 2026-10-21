/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1489 : Family 9 := level9.get ⟨221,by decide⟩
def sourceMap1489 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1489 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1489_checked : acceptsGraphIso
    (source (graph core1489) (root 9) 0 0) DegreeOneSmallSpectrum705.graph sourceMap1489=true := by decide +kernel
theorem fusedMap1489_checked : acceptsGraphIso
    (fused (graph core1489) (root 9) 0 0) DegreeOneSmallSpectrum531.graph fusedMap1489=true := by decide +kernel
theorem certified1489 : Certified (graph core1489) (root 9) 0 0 :=
  of_native_maps core1489 DegreeOneSmallSpectrum705.graph DegreeOneSmallSpectrum531.graph
    sourceMap1489 fusedMap1489 sourceMap1489_checked fusedMap1489_checked
    DegreeOneSmallComparisons.comparison1489
#print axioms sourceMap1489_checked
#print axioms fusedMap1489_checked
#print axioms certified1489
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
