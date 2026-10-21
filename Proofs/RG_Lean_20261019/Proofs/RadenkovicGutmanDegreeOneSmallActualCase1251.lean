/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1251 : Family 9 := level9.get ⟨32,by decide⟩
def sourceMap1251 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1251 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1251_checked : acceptsGraphIso
    (source (graph core1251) (root 9) 0 0) DegreeOneSmallSpectrum457.graph sourceMap1251=true := by decide +kernel
theorem fusedMap1251_checked : acceptsGraphIso
    (fused (graph core1251) (root 9) 0 0) DegreeOneSmallSpectrum391.graph fusedMap1251=true := by decide +kernel
theorem certified1251 : Certified (graph core1251) (root 9) 0 0 :=
  of_native_maps core1251 DegreeOneSmallSpectrum457.graph DegreeOneSmallSpectrum391.graph
    sourceMap1251 fusedMap1251 sourceMap1251_checked fusedMap1251_checked
    DegreeOneSmallComparisons.comparison1251
#print axioms sourceMap1251_checked
#print axioms fusedMap1251_checked
#print axioms certified1251
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
