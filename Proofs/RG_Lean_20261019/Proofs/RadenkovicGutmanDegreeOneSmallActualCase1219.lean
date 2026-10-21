/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1219 : Family 9 := level9.get ⟨13,by decide⟩
def sourceMap1219 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1219 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1219_checked : acceptsGraphIso
    (source (graph core1219) (root 9) 0 0) DegreeOneSmallSpectrum471.graph sourceMap1219=true := by decide +kernel
theorem fusedMap1219_checked : acceptsGraphIso
    (fused (graph core1219) (root 9) 0 0) DegreeOneSmallSpectrum377.graph fusedMap1219=true := by decide +kernel
theorem certified1219 : Certified (graph core1219) (root 9) 0 0 :=
  of_native_maps core1219 DegreeOneSmallSpectrum471.graph DegreeOneSmallSpectrum377.graph
    sourceMap1219 fusedMap1219 sourceMap1219_checked fusedMap1219_checked
    DegreeOneSmallComparisons.comparison1219
#print axioms sourceMap1219_checked
#print axioms fusedMap1219_checked
#print axioms certified1219
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
