/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1619 : Family 9 := level9.get ⟨361,by decide⟩
def sourceMap1619 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (sourceLabel 9 0 0 v)
def fusedMap1619 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1619_checked : acceptsGraphIso
    (source (graph core1619) (root 9) 0 0) DegreeOneSmallSpectrum698.graph sourceMap1619=true := by decide +kernel
theorem fusedMap1619_checked : acceptsGraphIso
    (fused (graph core1619) (root 9) 0 0) DegreeOneSmallSpectrum707.graph fusedMap1619=true := by decide +kernel
theorem certified1619 : Certified (graph core1619) (root 9) 0 0 :=
  of_native_maps core1619 DegreeOneSmallSpectrum698.graph DegreeOneSmallSpectrum707.graph
    sourceMap1619 fusedMap1619 sourceMap1619_checked fusedMap1619_checked
    DegreeOneSmallComparisons.comparison1619
#print axioms sourceMap1619_checked
#print axioms fusedMap1619_checked
#print axioms certified1619
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
