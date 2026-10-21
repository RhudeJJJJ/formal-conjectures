/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1743 : Family 9 := level9.get ⟨565,by decide⟩
def sourceMap1743 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 9 0 0 v)
def fusedMap1743 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1743_checked : acceptsGraphIso
    (source (graph core1743) (root 9) 0 0) SmallGeFourSpectrum217.graph sourceMap1743=true := by decide +kernel
theorem fusedMap1743_checked : acceptsGraphIso
    (fused (graph core1743) (root 9) 0 0) SmallGeFourSpectrum131.graph fusedMap1743=true := by decide +kernel
theorem certified1743 : Certified (graph core1743) (root 9) 0 0 :=
  of_native_maps core1743 SmallGeFourSpectrum217.graph SmallGeFourSpectrum131.graph
    sourceMap1743 fusedMap1743 sourceMap1743_checked fusedMap1743_checked
    DegreeOneSmallComparisons.comparison1743
#print axioms sourceMap1743_checked
#print axioms fusedMap1743_checked
#print axioms certified1743
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
