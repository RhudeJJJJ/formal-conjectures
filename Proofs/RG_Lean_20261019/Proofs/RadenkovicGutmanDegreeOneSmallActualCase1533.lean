/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1533 : Family 9 := level9.get ⟨262,by decide⟩
def sourceMap1533 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1533 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1533_checked : acceptsGraphIso
    (source (graph core1533) (root 9) 0 0) DegreeOneSmallSpectrum707.graph sourceMap1533=true := by decide +kernel
theorem fusedMap1533_checked : acceptsGraphIso
    (fused (graph core1533) (root 9) 0 0) DegreeOneSmallSpectrum572.graph fusedMap1533=true := by decide +kernel
theorem certified1533 : Certified (graph core1533) (root 9) 0 0 :=
  of_native_maps core1533 DegreeOneSmallSpectrum707.graph DegreeOneSmallSpectrum572.graph
    sourceMap1533 fusedMap1533 sourceMap1533_checked fusedMap1533_checked
    DegreeOneSmallComparisons.comparison1533
#print axioms sourceMap1533_checked
#print axioms fusedMap1533_checked
#print axioms certified1533
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
