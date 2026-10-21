/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1689 : Family 9 := level9.get ⟨450,by decide⟩
def sourceMap1689 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1689 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1689_checked : acceptsGraphIso
    (source (graph core1689) (root 9) 0 0) DegreeOneSmallSpectrum716.graph sourceMap1689=true := by decide +kernel
theorem fusedMap1689_checked : acceptsGraphIso
    (fused (graph core1689) (root 9) 0 0) SmallGeFourSpectrum189.graph fusedMap1689=true := by decide +kernel
theorem certified1689 : Certified (graph core1689) (root 9) 0 0 :=
  of_native_maps core1689 DegreeOneSmallSpectrum716.graph SmallGeFourSpectrum189.graph
    sourceMap1689 fusedMap1689 sourceMap1689_checked fusedMap1689_checked
    DegreeOneSmallComparisons.comparison1689
#print axioms sourceMap1689_checked
#print axioms fusedMap1689_checked
#print axioms certified1689
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
