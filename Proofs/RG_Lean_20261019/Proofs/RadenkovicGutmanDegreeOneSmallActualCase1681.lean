/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1681 : Family 9 := level9.get ⟨442,by decide⟩
def sourceMap1681 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (sourceLabel 9 0 0 v)
def fusedMap1681 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1681_checked : acceptsGraphIso
    (source (graph core1681) (root 9) 0 0) SmallGeFourSpectrum150.graph sourceMap1681=true := by decide +kernel
theorem fusedMap1681_checked : acceptsGraphIso
    (fused (graph core1681) (root 9) 0 0) SmallGeFourSpectrum188.graph fusedMap1681=true := by decide +kernel
theorem certified1681 : Certified (graph core1681) (root 9) 0 0 :=
  of_native_maps core1681 SmallGeFourSpectrum150.graph SmallGeFourSpectrum188.graph
    sourceMap1681 fusedMap1681 sourceMap1681_checked fusedMap1681_checked
    DegreeOneSmallComparisons.comparison1681
#print axioms sourceMap1681_checked
#print axioms fusedMap1681_checked
#print axioms certified1681
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
