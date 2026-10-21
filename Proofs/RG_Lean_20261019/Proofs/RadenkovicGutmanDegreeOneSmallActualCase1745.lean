/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1745 : Family 9 := level9.get ⟨569,by decide⟩
def sourceMap1745 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 9 0 0 v)
def fusedMap1745 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1745_checked : acceptsGraphIso
    (source (graph core1745) (root 9) 0 0) SmallGeFourSpectrum218.graph sourceMap1745=true := by decide +kernel
theorem fusedMap1745_checked : acceptsGraphIso
    (fused (graph core1745) (root 9) 0 0) SmallGeFourSpectrum132.graph fusedMap1745=true := by decide +kernel
theorem certified1745 : Certified (graph core1745) (root 9) 0 0 :=
  of_native_maps core1745 SmallGeFourSpectrum218.graph SmallGeFourSpectrum132.graph
    sourceMap1745 fusedMap1745 sourceMap1745_checked fusedMap1745_checked
    DegreeOneSmallComparisons.comparison1745
#print axioms sourceMap1745_checked
#print axioms fusedMap1745_checked
#print axioms certified1745
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
