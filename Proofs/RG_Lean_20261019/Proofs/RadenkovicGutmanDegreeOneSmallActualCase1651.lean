/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1651 : Family 9 := level9.get ⟨394,by decide⟩
def sourceMap1651 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 9 0 0 v)
def fusedMap1651 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1651_checked : acceptsGraphIso
    (source (graph core1651) (root 9) 0 0) SmallGeFourSpectrum142.graph sourceMap1651=true := by decide +kernel
theorem fusedMap1651_checked : acceptsGraphIso
    (fused (graph core1651) (root 9) 0 0) SmallGeFourSpectrum161.graph fusedMap1651=true := by decide +kernel
theorem certified1651 : Certified (graph core1651) (root 9) 0 0 :=
  of_native_maps core1651 SmallGeFourSpectrum142.graph SmallGeFourSpectrum161.graph
    sourceMap1651 fusedMap1651 sourceMap1651_checked fusedMap1651_checked
    DegreeOneSmallComparisons.comparison1651
#print axioms sourceMap1651_checked
#print axioms fusedMap1651_checked
#print axioms certified1651
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
