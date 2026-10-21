/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1579 : Family 9 := level9.get ⟨322,by decide⟩
def sourceMap1579 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1579 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1579_checked : acceptsGraphIso
    (source (graph core1579) (root 9) 0 0) DegreeOneSmallSpectrum610.graph sourceMap1579=true := by decide +kernel
theorem fusedMap1579_checked : acceptsGraphIso
    (fused (graph core1579) (root 9) 0 0) DegreeOneSmallSpectrum612.graph fusedMap1579=true := by decide +kernel
theorem certified1579 : Certified (graph core1579) (root 9) 0 0 :=
  of_native_maps core1579 DegreeOneSmallSpectrum610.graph DegreeOneSmallSpectrum612.graph
    sourceMap1579 fusedMap1579 sourceMap1579_checked fusedMap1579_checked
    DegreeOneSmallComparisons.comparison1579
#print axioms sourceMap1579_checked
#print axioms fusedMap1579_checked
#print axioms certified1579
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
