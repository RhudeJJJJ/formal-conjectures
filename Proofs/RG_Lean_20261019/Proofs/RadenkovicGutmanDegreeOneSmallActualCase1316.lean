/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1316 : Family 9 := level9.get ⟨77,by decide⟩
def sourceMap1316 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1316 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1316_checked : acceptsGraphIso
    (source (graph core1316) (root 9) 0 1) DegreeOneSmallSpectrum1383.graph sourceMap1316=true := by decide +kernel
theorem fusedMap1316_checked : acceptsGraphIso
    (fused (graph core1316) (root 9) 0 1) DegreeOneSmallSpectrum921.graph fusedMap1316=true := by decide +kernel
theorem certified1316 : Certified (graph core1316) (root 9) 0 1 :=
  of_native_maps core1316 DegreeOneSmallSpectrum1383.graph DegreeOneSmallSpectrum921.graph
    sourceMap1316 fusedMap1316 sourceMap1316_checked fusedMap1316_checked
    DegreeOneSmallComparisons.comparison1316
#print axioms sourceMap1316_checked
#print axioms fusedMap1316_checked
#print axioms certified1316
def sourceMap1316swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1316swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1316swap_checked : acceptsGraphIso
    (source (graph core1316) (root 9) 1 0) DegreeOneSmallSpectrum1383.graph sourceMap1316swap=true := by decide +kernel
theorem fusedMap1316swap_checked : acceptsGraphIso
    (fused (graph core1316) (root 9) 1 0) DegreeOneSmallSpectrum921.graph fusedMap1316swap=true := by decide +kernel
theorem certified1316swap : Certified (graph core1316) (root 9) 1 0 :=
  of_native_maps core1316 DegreeOneSmallSpectrum1383.graph DegreeOneSmallSpectrum921.graph
    sourceMap1316swap fusedMap1316swap sourceMap1316swap_checked fusedMap1316swap_checked
    DegreeOneSmallComparisons.comparison1316
#print axioms sourceMap1316swap_checked
#print axioms fusedMap1316swap_checked
#print axioms certified1316swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
