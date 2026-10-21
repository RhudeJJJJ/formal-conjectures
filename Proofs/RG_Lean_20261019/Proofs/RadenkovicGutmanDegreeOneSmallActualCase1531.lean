/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1531 : Family 9 := level9.get ⟨260,by decide⟩
def sourceMap1531 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1531 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1531_checked : acceptsGraphIso
    (source (graph core1531) (root 9) 0 0) DegreeOneSmallSpectrum743.graph sourceMap1531=true := by decide +kernel
theorem fusedMap1531_checked : acceptsGraphIso
    (fused (graph core1531) (root 9) 0 0) DegreeOneSmallSpectrum570.graph fusedMap1531=true := by decide +kernel
theorem certified1531 : Certified (graph core1531) (root 9) 0 0 :=
  of_native_maps core1531 DegreeOneSmallSpectrum743.graph DegreeOneSmallSpectrum570.graph
    sourceMap1531 fusedMap1531 sourceMap1531_checked fusedMap1531_checked
    DegreeOneSmallComparisons.comparison1531
#print axioms sourceMap1531_checked
#print axioms fusedMap1531_checked
#print axioms certified1531
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
