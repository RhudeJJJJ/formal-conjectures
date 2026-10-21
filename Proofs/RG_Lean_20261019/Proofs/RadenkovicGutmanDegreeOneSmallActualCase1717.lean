/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1717 : Family 9 := level9.get ⟨499,by decide⟩
def sourceMap1717 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,8,2,3] (sourceLabel 9 0 0 v)
def fusedMap1717 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1717_checked : acceptsGraphIso
    (source (graph core1717) (root 9) 0 0) SmallGeFourSpectrum140.graph sourceMap1717=true := by decide +kernel
theorem fusedMap1717_checked : acceptsGraphIso
    (fused (graph core1717) (root 9) 0 0) SmallGeFourSpectrum194.graph fusedMap1717=true := by decide +kernel
theorem certified1717 : Certified (graph core1717) (root 9) 0 0 :=
  of_native_maps core1717 SmallGeFourSpectrum140.graph SmallGeFourSpectrum194.graph
    sourceMap1717 fusedMap1717 sourceMap1717_checked fusedMap1717_checked
    DegreeOneSmallComparisons.comparison1717
#print axioms sourceMap1717_checked
#print axioms fusedMap1717_checked
#print axioms certified1717
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
