/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1635 : Family 9 := level9.get ⟨376,by decide⟩
def sourceMap1635 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1635 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1635_checked : acceptsGraphIso
    (source (graph core1635) (root 9) 0 0) DegreeOneSmallSpectrum692.graph sourceMap1635=true := by decide +kernel
theorem fusedMap1635_checked : acceptsGraphIso
    (fused (graph core1635) (root 9) 0 0) DegreeOneSmallSpectrum743.graph fusedMap1635=true := by decide +kernel
theorem certified1635 : Certified (graph core1635) (root 9) 0 0 :=
  of_native_maps core1635 DegreeOneSmallSpectrum692.graph DegreeOneSmallSpectrum743.graph
    sourceMap1635 fusedMap1635 sourceMap1635_checked fusedMap1635_checked
    DegreeOneSmallComparisons.comparison1635
#print axioms sourceMap1635_checked
#print axioms fusedMap1635_checked
#print axioms certified1635
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
