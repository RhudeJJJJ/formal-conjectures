/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1677 : Family 9 := level9.get ⟨439,by decide⟩
def sourceMap1677 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 9 0 0 v)
def fusedMap1677 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1677_checked : acceptsGraphIso
    (source (graph core1677) (root 9) 0 0) SmallGeFourSpectrum152.graph sourceMap1677=true := by decide +kernel
theorem fusedMap1677_checked : acceptsGraphIso
    (fused (graph core1677) (root 9) 0 0) SmallGeFourSpectrum183.graph fusedMap1677=true := by decide +kernel
theorem certified1677 : Certified (graph core1677) (root 9) 0 0 :=
  of_native_maps core1677 SmallGeFourSpectrum152.graph SmallGeFourSpectrum183.graph
    sourceMap1677 fusedMap1677 sourceMap1677_checked fusedMap1677_checked
    DegreeOneSmallComparisons.comparison1677
#print axioms sourceMap1677_checked
#print axioms fusedMap1677_checked
#print axioms certified1677
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
