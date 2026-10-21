/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1499 : Family 9 := level9.get ⟨229,by decide⟩
def sourceMap1499 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1499 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1499_checked : acceptsGraphIso
    (source (graph core1499) (root 9) 0 0) DegreeOneSmallSpectrum739.graph sourceMap1499=true := by decide +kernel
theorem fusedMap1499_checked : acceptsGraphIso
    (fused (graph core1499) (root 9) 0 0) DegreeOneSmallSpectrum539.graph fusedMap1499=true := by decide +kernel
theorem certified1499 : Certified (graph core1499) (root 9) 0 0 :=
  of_native_maps core1499 DegreeOneSmallSpectrum739.graph DegreeOneSmallSpectrum539.graph
    sourceMap1499 fusedMap1499 sourceMap1499_checked fusedMap1499_checked
    DegreeOneSmallComparisons.comparison1499
#print axioms sourceMap1499_checked
#print axioms fusedMap1499_checked
#print axioms certified1499
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
