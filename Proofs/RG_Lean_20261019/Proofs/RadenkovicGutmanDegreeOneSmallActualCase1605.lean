/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1605 : Family 9 := level9.get ⟨344,by decide⟩
def sourceMap1605 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (sourceLabel 9 0 0 v)
def fusedMap1605 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1605_checked : acceptsGraphIso
    (source (graph core1605) (root 9) 0 0) DegreeOneSmallSpectrum659.graph sourceMap1605=true := by decide +kernel
theorem fusedMap1605_checked : acceptsGraphIso
    (fused (graph core1605) (root 9) 0 0) DegreeOneSmallSpectrum671.graph fusedMap1605=true := by decide +kernel
theorem certified1605 : Certified (graph core1605) (root 9) 0 0 :=
  of_native_maps core1605 DegreeOneSmallSpectrum659.graph DegreeOneSmallSpectrum671.graph
    sourceMap1605 fusedMap1605 sourceMap1605_checked fusedMap1605_checked
    DegreeOneSmallComparisons.comparison1605
#print axioms sourceMap1605_checked
#print axioms fusedMap1605_checked
#print axioms certified1605
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
