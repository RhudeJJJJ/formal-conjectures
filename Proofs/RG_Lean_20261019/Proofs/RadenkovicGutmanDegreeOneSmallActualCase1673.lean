/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1673 : Family 9 := level9.get ⟨430,by decide⟩
def sourceMap1673 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1673 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1673_checked : acceptsGraphIso
    (source (graph core1673) (root 9) 0 0) DegreeOneSmallSpectrum715.graph sourceMap1673=true := by decide +kernel
theorem fusedMap1673_checked : acceptsGraphIso
    (fused (graph core1673) (root 9) 0 0) SmallGeFourSpectrum177.graph fusedMap1673=true := by decide +kernel
theorem certified1673 : Certified (graph core1673) (root 9) 0 0 :=
  of_native_maps core1673 DegreeOneSmallSpectrum715.graph SmallGeFourSpectrum177.graph
    sourceMap1673 fusedMap1673 sourceMap1673_checked fusedMap1673_checked
    DegreeOneSmallComparisons.comparison1673
#print axioms sourceMap1673_checked
#print axioms fusedMap1673_checked
#print axioms certified1673
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
