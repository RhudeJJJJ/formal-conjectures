/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1595 : Family 9 := level9.get ⟨335,by decide⟩
def sourceMap1595 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1595 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1595_checked : acceptsGraphIso
    (source (graph core1595) (root 9) 0 0) DegreeOneSmallSpectrum645.graph sourceMap1595=true := by decide +kernel
theorem fusedMap1595_checked : acceptsGraphIso
    (fused (graph core1595) (root 9) 0 0) DegreeOneSmallSpectrum649.graph fusedMap1595=true := by decide +kernel
theorem certified1595 : Certified (graph core1595) (root 9) 0 0 :=
  of_native_maps core1595 DegreeOneSmallSpectrum645.graph DegreeOneSmallSpectrum649.graph
    sourceMap1595 fusedMap1595 sourceMap1595_checked fusedMap1595_checked
    DegreeOneSmallComparisons.comparison1595
#print axioms sourceMap1595_checked
#print axioms fusedMap1595_checked
#print axioms certified1595
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
