/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1633 : Family 9 := level9.get ⟨375,by decide⟩
def sourceMap1633 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1633 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1633_checked : acceptsGraphIso
    (source (graph core1633) (root 9) 0 0) DegreeOneSmallSpectrum678.graph sourceMap1633=true := by decide +kernel
theorem fusedMap1633_checked : acceptsGraphIso
    (fused (graph core1633) (root 9) 0 0) DegreeOneSmallSpectrum742.graph fusedMap1633=true := by decide +kernel
theorem certified1633 : Certified (graph core1633) (root 9) 0 0 :=
  of_native_maps core1633 DegreeOneSmallSpectrum678.graph DegreeOneSmallSpectrum742.graph
    sourceMap1633 fusedMap1633 sourceMap1633_checked fusedMap1633_checked
    DegreeOneSmallComparisons.comparison1633
#print axioms sourceMap1633_checked
#print axioms fusedMap1633_checked
#print axioms certified1633
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
