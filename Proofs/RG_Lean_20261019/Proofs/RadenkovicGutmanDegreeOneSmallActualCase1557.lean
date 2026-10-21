/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1557 : Family 9 := level9.get ⟨289,by decide⟩
def sourceMap1557 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,8,9,10,11,1,2,3,4,6,7] (sourceLabel 9 0 0 v)
def fusedMap1557 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,8,9,10,11,1,2,3,4,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1557_checked : acceptsGraphIso
    (source (graph core1557) (root 9) 0 0) DegreeOneSmallSpectrum536.graph sourceMap1557=true := by decide +kernel
theorem fusedMap1557_checked : acceptsGraphIso
    (fused (graph core1557) (root 9) 0 0) DegreeOneSmallSpectrum535.graph fusedMap1557=true := by decide +kernel
theorem certified1557 : Certified (graph core1557) (root 9) 0 0 :=
  of_native_maps core1557 DegreeOneSmallSpectrum536.graph DegreeOneSmallSpectrum535.graph
    sourceMap1557 fusedMap1557 sourceMap1557_checked fusedMap1557_checked
    DegreeOneSmallComparisons.comparison1557
#print axioms sourceMap1557_checked
#print axioms fusedMap1557_checked
#print axioms certified1557
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
