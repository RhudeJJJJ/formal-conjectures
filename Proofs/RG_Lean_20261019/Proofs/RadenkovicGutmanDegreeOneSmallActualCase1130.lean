/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1130 : Family 8 := level8.get ⟨167,by decide⟩
def sourceMap1130 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1130 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1130_checked : acceptsGraphIso
    (source (graph core1130) (root 8) 1 1) DegreeOneSmallSpectrum1930.graph sourceMap1130=true := by decide +kernel
theorem fusedMap1130_checked : acceptsGraphIso
    (fused (graph core1130) (root 8) 1 1) DegreeOneSmallSpectrum1481.graph fusedMap1130=true := by decide +kernel
theorem certified1130 : Certified (graph core1130) (root 8) 1 1 :=
  of_native_maps core1130 DegreeOneSmallSpectrum1930.graph DegreeOneSmallSpectrum1481.graph
    sourceMap1130 fusedMap1130 sourceMap1130_checked fusedMap1130_checked
    DegreeOneSmallComparisons.comparison1130
#print axioms sourceMap1130_checked
#print axioms fusedMap1130_checked
#print axioms certified1130
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
