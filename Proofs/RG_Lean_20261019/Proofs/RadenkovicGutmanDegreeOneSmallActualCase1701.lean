/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1701 : Family 9 := level9.get ⟨465,by decide⟩
def sourceMap1701 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 9 0 0 v)
def fusedMap1701 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1701_checked : acceptsGraphIso
    (source (graph core1701) (root 9) 0 0) SmallGeFourSpectrum143.graph sourceMap1701=true := by decide +kernel
theorem fusedMap1701_checked : acceptsGraphIso
    (fused (graph core1701) (root 9) 0 0) SmallGeFourSpectrum190.graph fusedMap1701=true := by decide +kernel
theorem certified1701 : Certified (graph core1701) (root 9) 0 0 :=
  of_native_maps core1701 SmallGeFourSpectrum143.graph SmallGeFourSpectrum190.graph
    sourceMap1701 fusedMap1701 sourceMap1701_checked fusedMap1701_checked
    DegreeOneSmallComparisons.comparison1701
#print axioms sourceMap1701_checked
#print axioms fusedMap1701_checked
#print axioms certified1701
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
