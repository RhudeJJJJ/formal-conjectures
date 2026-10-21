/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1527 : Family 9 := level9.get ⟨258,by decide⟩
def sourceMap1527 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1527 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1527_checked : acceptsGraphIso
    (source (graph core1527) (root 9) 0 0) DegreeOneSmallSpectrum768.graph sourceMap1527=true := by decide +kernel
theorem fusedMap1527_checked : acceptsGraphIso
    (fused (graph core1527) (root 9) 0 0) DegreeOneSmallSpectrum568.graph fusedMap1527=true := by decide +kernel
theorem certified1527 : Certified (graph core1527) (root 9) 0 0 :=
  of_native_maps core1527 DegreeOneSmallSpectrum768.graph DegreeOneSmallSpectrum568.graph
    sourceMap1527 fusedMap1527 sourceMap1527_checked fusedMap1527_checked
    DegreeOneSmallComparisons.comparison1527
#print axioms sourceMap1527_checked
#print axioms fusedMap1527_checked
#print axioms certified1527
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
