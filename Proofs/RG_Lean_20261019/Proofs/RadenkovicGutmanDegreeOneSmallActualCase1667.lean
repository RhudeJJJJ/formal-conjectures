/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1667 : Family 9 := level9.get ⟨426,by decide⟩
def sourceMap1667 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1667 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1667_checked : acceptsGraphIso
    (source (graph core1667) (root 9) 0 0) DegreeOneSmallSpectrum795.graph sourceMap1667=true := by decide +kernel
theorem fusedMap1667_checked : acceptsGraphIso
    (fused (graph core1667) (root 9) 0 0) DegreeOneSmallSpectrum794.graph fusedMap1667=true := by decide +kernel
theorem certified1667 : Certified (graph core1667) (root 9) 0 0 :=
  of_native_maps core1667 DegreeOneSmallSpectrum795.graph DegreeOneSmallSpectrum794.graph
    sourceMap1667 fusedMap1667 sourceMap1667_checked fusedMap1667_checked
    DegreeOneSmallComparisons.comparison1667
#print axioms sourceMap1667_checked
#print axioms fusedMap1667_checked
#print axioms certified1667
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
