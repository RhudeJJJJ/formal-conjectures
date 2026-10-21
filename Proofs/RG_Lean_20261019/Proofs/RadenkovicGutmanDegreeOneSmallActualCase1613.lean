/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1613 : Family 9 := level9.get ⟨357,by decide⟩
def sourceMap1613 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1613 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1613_checked : acceptsGraphIso
    (source (graph core1613) (root 9) 0 0) DegreeOneSmallSpectrum685.graph sourceMap1613=true := by decide +kernel
theorem fusedMap1613_checked : acceptsGraphIso
    (fused (graph core1613) (root 9) 0 0) DegreeOneSmallSpectrum687.graph fusedMap1613=true := by decide +kernel
theorem certified1613 : Certified (graph core1613) (root 9) 0 0 :=
  of_native_maps core1613 DegreeOneSmallSpectrum685.graph DegreeOneSmallSpectrum687.graph
    sourceMap1613 fusedMap1613 sourceMap1613_checked fusedMap1613_checked
    DegreeOneSmallComparisons.comparison1613
#print axioms sourceMap1613_checked
#print axioms fusedMap1613_checked
#print axioms certified1613
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
