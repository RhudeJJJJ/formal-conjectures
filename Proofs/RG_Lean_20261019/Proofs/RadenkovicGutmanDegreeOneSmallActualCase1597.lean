/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1597 : Family 9 := level9.get ⟨337,by decide⟩
def sourceMap1597 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1597 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1597_checked : acceptsGraphIso
    (source (graph core1597) (root 9) 0 0) DegreeOneSmallSpectrum650.graph sourceMap1597=true := by decide +kernel
theorem fusedMap1597_checked : acceptsGraphIso
    (fused (graph core1597) (root 9) 0 0) DegreeOneSmallSpectrum656.graph fusedMap1597=true := by decide +kernel
theorem certified1597 : Certified (graph core1597) (root 9) 0 0 :=
  of_native_maps core1597 DegreeOneSmallSpectrum650.graph DegreeOneSmallSpectrum656.graph
    sourceMap1597 fusedMap1597 sourceMap1597_checked fusedMap1597_checked
    DegreeOneSmallComparisons.comparison1597
#print axioms sourceMap1597_checked
#print axioms fusedMap1597_checked
#print axioms certified1597
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
