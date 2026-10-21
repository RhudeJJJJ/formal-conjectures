/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1469 : Family 9 := level9.get ⟨205,by decide⟩
def sourceMap1469 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1469 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1469_checked : acceptsGraphIso
    (source (graph core1469) (root 9) 0 0) DegreeOneSmallSpectrum755.graph sourceMap1469=true := by decide +kernel
theorem fusedMap1469_checked : acceptsGraphIso
    (fused (graph core1469) (root 9) 0 0) DegreeOneSmallSpectrum507.graph fusedMap1469=true := by decide +kernel
theorem certified1469 : Certified (graph core1469) (root 9) 0 0 :=
  of_native_maps core1469 DegreeOneSmallSpectrum755.graph DegreeOneSmallSpectrum507.graph
    sourceMap1469 fusedMap1469 sourceMap1469_checked fusedMap1469_checked
    DegreeOneSmallComparisons.comparison1469
#print axioms sourceMap1469_checked
#print axioms fusedMap1469_checked
#print axioms certified1469
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
