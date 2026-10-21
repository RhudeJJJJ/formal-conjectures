/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1693 : Family 9 := level9.get ⟨459,by decide⟩
def sourceMap1693 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1693 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1693_checked : acceptsGraphIso
    (source (graph core1693) (root 9) 0 0) DegreeOneSmallSpectrum818.graph sourceMap1693=true := by decide +kernel
theorem fusedMap1693_checked : acceptsGraphIso
    (fused (graph core1693) (root 9) 0 0) DegreeOneSmallSpectrum816.graph fusedMap1693=true := by decide +kernel
theorem certified1693 : Certified (graph core1693) (root 9) 0 0 :=
  of_native_maps core1693 DegreeOneSmallSpectrum818.graph DegreeOneSmallSpectrum816.graph
    sourceMap1693 fusedMap1693 sourceMap1693_checked fusedMap1693_checked
    DegreeOneSmallComparisons.comparison1693
#print axioms sourceMap1693_checked
#print axioms fusedMap1693_checked
#print axioms certified1693
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
