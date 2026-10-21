/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1561 : Family 9 := level9.get ⟨292,by decide⟩
def sourceMap1561 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,1,0,9,10,11,2,3,4,5,7,8] (sourceLabel 9 0 0 v)
def fusedMap1561 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1561_checked : acceptsGraphIso
    (source (graph core1561) (root 9) 0 0) DegreeOneSmallSpectrum630.graph sourceMap1561=true := by decide +kernel
theorem fusedMap1561_checked : acceptsGraphIso
    (fused (graph core1561) (root 9) 0 0) DegreeOneSmallSpectrum564.graph fusedMap1561=true := by decide +kernel
theorem certified1561 : Certified (graph core1561) (root 9) 0 0 :=
  of_native_maps core1561 DegreeOneSmallSpectrum630.graph DegreeOneSmallSpectrum564.graph
    sourceMap1561 fusedMap1561 sourceMap1561_checked fusedMap1561_checked
    DegreeOneSmallComparisons.comparison1561
#print axioms sourceMap1561_checked
#print axioms fusedMap1561_checked
#print axioms certified1561
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
