/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1283 : Family 9 := level9.get ⟨55,by decide⟩
def sourceMap1283 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1283 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1283_checked : acceptsGraphIso
    (source (graph core1283) (root 9) 0 0) DegreeOneSmallSpectrum461.graph sourceMap1283=true := by decide +kernel
theorem fusedMap1283_checked : acceptsGraphIso
    (fused (graph core1283) (root 9) 0 0) DegreeOneSmallSpectrum464.graph fusedMap1283=true := by decide +kernel
theorem certified1283 : Certified (graph core1283) (root 9) 0 0 :=
  of_native_maps core1283 DegreeOneSmallSpectrum461.graph DegreeOneSmallSpectrum464.graph
    sourceMap1283 fusedMap1283 sourceMap1283_checked fusedMap1283_checked
    DegreeOneSmallComparisons.comparison1283
#print axioms sourceMap1283_checked
#print axioms fusedMap1283_checked
#print axioms certified1283
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
