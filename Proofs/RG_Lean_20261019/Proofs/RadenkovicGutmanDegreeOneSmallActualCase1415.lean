/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1415 : Family 9 := level9.get ⟨158,by decide⟩
def sourceMap1415 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1415 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1415_checked : acceptsGraphIso
    (source (graph core1415) (root 9) 0 0) DegreeOneSmallSpectrum701.graph sourceMap1415=true := by decide +kernel
theorem fusedMap1415_checked : acceptsGraphIso
    (fused (graph core1415) (root 9) 0 0) DegreeOneSmallSpectrum430.graph fusedMap1415=true := by decide +kernel
theorem certified1415 : Certified (graph core1415) (root 9) 0 0 :=
  of_native_maps core1415 DegreeOneSmallSpectrum701.graph DegreeOneSmallSpectrum430.graph
    sourceMap1415 fusedMap1415 sourceMap1415_checked fusedMap1415_checked
    DegreeOneSmallComparisons.comparison1415
#print axioms sourceMap1415_checked
#print axioms fusedMap1415_checked
#print axioms certified1415
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
