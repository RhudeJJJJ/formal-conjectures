/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1683 : Family 9 := level9.get ⟨446,by decide⟩
def sourceMap1683 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1683 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1683_checked : acceptsGraphIso
    (source (graph core1683) (root 9) 0 0) DegreeOneSmallSpectrum809.graph sourceMap1683=true := by decide +kernel
theorem fusedMap1683_checked : acceptsGraphIso
    (fused (graph core1683) (root 9) 0 0) DegreeOneSmallSpectrum808.graph fusedMap1683=true := by decide +kernel
theorem certified1683 : Certified (graph core1683) (root 9) 0 0 :=
  of_native_maps core1683 DegreeOneSmallSpectrum809.graph DegreeOneSmallSpectrum808.graph
    sourceMap1683 fusedMap1683 sourceMap1683_checked fusedMap1683_checked
    DegreeOneSmallComparisons.comparison1683
#print axioms sourceMap1683_checked
#print axioms fusedMap1683_checked
#print axioms certified1683
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
