/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1703 : Family 9 := level9.get ⟨469,by decide⟩
def sourceMap1703 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 9 0 0 v)
def fusedMap1703 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1703_checked : acceptsGraphIso
    (source (graph core1703) (root 9) 0 0) SmallGeFourSpectrum148.graph sourceMap1703=true := by decide +kernel
theorem fusedMap1703_checked : acceptsGraphIso
    (fused (graph core1703) (root 9) 0 0) SmallGeFourSpectrum191.graph fusedMap1703=true := by decide +kernel
theorem certified1703 : Certified (graph core1703) (root 9) 0 0 :=
  of_native_maps core1703 SmallGeFourSpectrum148.graph SmallGeFourSpectrum191.graph
    sourceMap1703 fusedMap1703 sourceMap1703_checked fusedMap1703_checked
    DegreeOneSmallComparisons.comparison1703
#print axioms sourceMap1703_checked
#print axioms fusedMap1703_checked
#print axioms certified1703
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
