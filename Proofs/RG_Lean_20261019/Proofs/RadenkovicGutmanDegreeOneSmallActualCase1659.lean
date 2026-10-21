/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1659 : Family 9 := level9.get ⟨418,by decide⟩
def sourceMap1659 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1659 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1659_checked : acceptsGraphIso
    (source (graph core1659) (root 9) 0 0) SmallGeFourSpectrum156.graph sourceMap1659=true := by decide +kernel
theorem fusedMap1659_checked : acceptsGraphIso
    (fused (graph core1659) (root 9) 0 0) SmallGeFourSpectrum169.graph fusedMap1659=true := by decide +kernel
theorem certified1659 : Certified (graph core1659) (root 9) 0 0 :=
  of_native_maps core1659 SmallGeFourSpectrum156.graph SmallGeFourSpectrum169.graph
    sourceMap1659 fusedMap1659 sourceMap1659_checked fusedMap1659_checked
    DegreeOneSmallComparisons.comparison1659
#print axioms sourceMap1659_checked
#print axioms fusedMap1659_checked
#print axioms certified1659
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
