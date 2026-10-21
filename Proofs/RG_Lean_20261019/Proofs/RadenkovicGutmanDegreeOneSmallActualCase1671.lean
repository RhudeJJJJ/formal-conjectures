/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1671 : Family 9 := level9.get ⟨428,by decide⟩
def sourceMap1671 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1671 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1671_checked : acceptsGraphIso
    (source (graph core1671) (root 9) 0 0) DegreeOneSmallSpectrum694.graph sourceMap1671=true := by decide +kernel
theorem fusedMap1671_checked : acceptsGraphIso
    (fused (graph core1671) (root 9) 0 0) DegreeOneSmallSpectrum796.graph fusedMap1671=true := by decide +kernel
theorem certified1671 : Certified (graph core1671) (root 9) 0 0 :=
  of_native_maps core1671 DegreeOneSmallSpectrum694.graph DegreeOneSmallSpectrum796.graph
    sourceMap1671 fusedMap1671 sourceMap1671_checked fusedMap1671_checked
    DegreeOneSmallComparisons.comparison1671
#print axioms sourceMap1671_checked
#print axioms fusedMap1671_checked
#print axioms certified1671
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
