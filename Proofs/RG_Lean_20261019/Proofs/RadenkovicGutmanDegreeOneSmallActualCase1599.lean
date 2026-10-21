/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1599 : Family 9 := level9.get ⟨338,by decide⟩
def sourceMap1599 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1599 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1599_checked : acceptsGraphIso
    (source (graph core1599) (root 9) 0 0) DegreeOneSmallSpectrum651.graph sourceMap1599=true := by decide +kernel
theorem fusedMap1599_checked : acceptsGraphIso
    (fused (graph core1599) (root 9) 0 0) DegreeOneSmallSpectrum657.graph fusedMap1599=true := by decide +kernel
theorem certified1599 : Certified (graph core1599) (root 9) 0 0 :=
  of_native_maps core1599 DegreeOneSmallSpectrum651.graph DegreeOneSmallSpectrum657.graph
    sourceMap1599 fusedMap1599 sourceMap1599_checked fusedMap1599_checked
    DegreeOneSmallComparisons.comparison1599
#print axioms sourceMap1599_checked
#print axioms fusedMap1599_checked
#print axioms certified1599
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
