/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1591 : Family 9 := level9.get ⟨332,by decide⟩
def sourceMap1591 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1591 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1591_checked : acceptsGraphIso
    (source (graph core1591) (root 9) 0 0) DegreeOneSmallSpectrum636.graph sourceMap1591=true := by decide +kernel
theorem fusedMap1591_checked : acceptsGraphIso
    (fused (graph core1591) (root 9) 0 0) DegreeOneSmallSpectrum640.graph fusedMap1591=true := by decide +kernel
theorem certified1591 : Certified (graph core1591) (root 9) 0 0 :=
  of_native_maps core1591 DegreeOneSmallSpectrum636.graph DegreeOneSmallSpectrum640.graph
    sourceMap1591 fusedMap1591 sourceMap1591_checked fusedMap1591_checked
    DegreeOneSmallComparisons.comparison1591
#print axioms sourceMap1591_checked
#print axioms fusedMap1591_checked
#print axioms certified1591
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
