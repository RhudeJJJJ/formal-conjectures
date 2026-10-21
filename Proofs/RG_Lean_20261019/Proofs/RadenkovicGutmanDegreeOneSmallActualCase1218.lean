/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1218 : Family 9 := level9.get ⟨12,by decide⟩
def sourceMap1218 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1218 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1218_checked : acceptsGraphIso
    (source (graph core1218) (root 9) 0 1) DegreeOneSmallSpectrum891.graph sourceMap1218=true := by decide +kernel
theorem fusedMap1218_checked : acceptsGraphIso
    (fused (graph core1218) (root 9) 0 1) DegreeOneSmallSpectrum894.graph fusedMap1218=true := by decide +kernel
theorem certified1218 : Certified (graph core1218) (root 9) 0 1 :=
  of_native_maps core1218 DegreeOneSmallSpectrum891.graph DegreeOneSmallSpectrum894.graph
    sourceMap1218 fusedMap1218 sourceMap1218_checked fusedMap1218_checked
    DegreeOneSmallComparisons.comparison1218
#print axioms sourceMap1218_checked
#print axioms fusedMap1218_checked
#print axioms certified1218
def sourceMap1218swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1218swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1218swap_checked : acceptsGraphIso
    (source (graph core1218) (root 9) 1 0) DegreeOneSmallSpectrum891.graph sourceMap1218swap=true := by decide +kernel
theorem fusedMap1218swap_checked : acceptsGraphIso
    (fused (graph core1218) (root 9) 1 0) DegreeOneSmallSpectrum894.graph fusedMap1218swap=true := by decide +kernel
theorem certified1218swap : Certified (graph core1218) (root 9) 1 0 :=
  of_native_maps core1218 DegreeOneSmallSpectrum891.graph DegreeOneSmallSpectrum894.graph
    sourceMap1218swap fusedMap1218swap sourceMap1218swap_checked fusedMap1218swap_checked
    DegreeOneSmallComparisons.comparison1218
#print axioms sourceMap1218swap_checked
#print axioms fusedMap1218swap_checked
#print axioms certified1218swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
