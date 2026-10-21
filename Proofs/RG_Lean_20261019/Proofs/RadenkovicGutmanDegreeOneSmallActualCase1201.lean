/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1201 : Family 9 := level9.get ⟨3,by decide⟩
def sourceMap1201 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1201 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1201_checked : acceptsGraphIso
    (source (graph core1201) (root 9) 0 0) DegreeOneSmallSpectrum376.graph sourceMap1201=true := by decide +kernel
theorem fusedMap1201_checked : acceptsGraphIso
    (fused (graph core1201) (root 9) 0 0) DegreeOneSmallSpectrum392.graph fusedMap1201=true := by decide +kernel
theorem certified1201 : Certified (graph core1201) (root 9) 0 0 :=
  of_native_maps core1201 DegreeOneSmallSpectrum376.graph DegreeOneSmallSpectrum392.graph
    sourceMap1201 fusedMap1201 sourceMap1201_checked fusedMap1201_checked
    DegreeOneSmallComparisons.comparison1201
#print axioms sourceMap1201_checked
#print axioms fusedMap1201_checked
#print axioms certified1201
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
