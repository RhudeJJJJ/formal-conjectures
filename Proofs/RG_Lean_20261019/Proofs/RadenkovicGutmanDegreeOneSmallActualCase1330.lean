/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1330 : Family 9 := level9.get ⟨86,by decide⟩
def sourceMap1330 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1330 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1330_checked : acceptsGraphIso
    (source (graph core1330) (root 9) 0 1) DegreeOneSmallSpectrum1426.graph sourceMap1330=true := by decide +kernel
theorem fusedMap1330_checked : acceptsGraphIso
    (fused (graph core1330) (root 9) 0 1) DegreeOneSmallSpectrum934.graph fusedMap1330=true := by decide +kernel
theorem certified1330 : Certified (graph core1330) (root 9) 0 1 :=
  of_native_maps core1330 DegreeOneSmallSpectrum1426.graph DegreeOneSmallSpectrum934.graph
    sourceMap1330 fusedMap1330 sourceMap1330_checked fusedMap1330_checked
    DegreeOneSmallComparisons.comparison1330
#print axioms sourceMap1330_checked
#print axioms fusedMap1330_checked
#print axioms certified1330
def sourceMap1330swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1330swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1330swap_checked : acceptsGraphIso
    (source (graph core1330) (root 9) 1 0) DegreeOneSmallSpectrum1426.graph sourceMap1330swap=true := by decide +kernel
theorem fusedMap1330swap_checked : acceptsGraphIso
    (fused (graph core1330) (root 9) 1 0) DegreeOneSmallSpectrum934.graph fusedMap1330swap=true := by decide +kernel
theorem certified1330swap : Certified (graph core1330) (root 9) 1 0 :=
  of_native_maps core1330 DegreeOneSmallSpectrum1426.graph DegreeOneSmallSpectrum934.graph
    sourceMap1330swap fusedMap1330swap sourceMap1330swap_checked fusedMap1330swap_checked
    DegreeOneSmallComparisons.comparison1330
#print axioms sourceMap1330swap_checked
#print axioms fusedMap1330swap_checked
#print axioms certified1330swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
