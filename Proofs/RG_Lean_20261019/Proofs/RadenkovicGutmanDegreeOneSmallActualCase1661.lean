/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1661 : Family 9 := level9.get ⟨419,by decide⟩
def sourceMap1661 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 9 0 0 v)
def fusedMap1661 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1661_checked : acceptsGraphIso
    (source (graph core1661) (root 9) 0 0) SmallGeFourSpectrum151.graph sourceMap1661=true := by decide +kernel
theorem fusedMap1661_checked : acceptsGraphIso
    (fused (graph core1661) (root 9) 0 0) SmallGeFourSpectrum173.graph fusedMap1661=true := by decide +kernel
theorem certified1661 : Certified (graph core1661) (root 9) 0 0 :=
  of_native_maps core1661 SmallGeFourSpectrum151.graph SmallGeFourSpectrum173.graph
    sourceMap1661 fusedMap1661 sourceMap1661_checked fusedMap1661_checked
    DegreeOneSmallComparisons.comparison1661
#print axioms sourceMap1661_checked
#print axioms fusedMap1661_checked
#print axioms certified1661
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
