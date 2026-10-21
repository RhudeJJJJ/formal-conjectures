/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1545 : Family 9 := level9.get ⟨275,by decide⟩
def sourceMap1545 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,7,8,9,10,11,1,2,3,5,6] (sourceLabel 9 0 0 v)
def fusedMap1545 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1545_checked : acceptsGraphIso
    (source (graph core1545) (root 9) 0 0) DegreeOneSmallSpectrum566.graph sourceMap1545=true := by decide +kernel
theorem fusedMap1545_checked : acceptsGraphIso
    (fused (graph core1545) (root 9) 0 0) DegreeOneSmallSpectrum562.graph fusedMap1545=true := by decide +kernel
theorem certified1545 : Certified (graph core1545) (root 9) 0 0 :=
  of_native_maps core1545 DegreeOneSmallSpectrum566.graph DegreeOneSmallSpectrum562.graph
    sourceMap1545 fusedMap1545 sourceMap1545_checked fusedMap1545_checked
    DegreeOneSmallComparisons.comparison1545
#print axioms sourceMap1545_checked
#print axioms fusedMap1545_checked
#print axioms certified1545
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
