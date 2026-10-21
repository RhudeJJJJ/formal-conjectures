/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2130 : Family 10 := level10.get ⟨570,by decide⟩
def sourceMap2130 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 10 0 0 v)
def fusedMap2130 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2130_checked : acceptsGraphIso
    (source (graph core2130) (root 10) 0 0) DegreeOneSmallSpectrum1758.graph sourceMap2130=true := by decide +kernel
theorem fusedMap2130_checked : acceptsGraphIso
    (fused (graph core2130) (root 10) 0 0) DegreeOneSmallSpectrum1100.graph fusedMap2130=true := by decide +kernel
theorem certified2130 : Certified (graph core2130) (root 10) 0 0 :=
  of_native_maps core2130 DegreeOneSmallSpectrum1758.graph DegreeOneSmallSpectrum1100.graph
    sourceMap2130 fusedMap2130 sourceMap2130_checked fusedMap2130_checked
    DegreeOneSmallComparisons.comparison2130
#print axioms sourceMap2130_checked
#print axioms fusedMap2130_checked
#print axioms certified2130
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
