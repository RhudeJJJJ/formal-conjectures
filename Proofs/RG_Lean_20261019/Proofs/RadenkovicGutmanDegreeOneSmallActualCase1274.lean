/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1274 : Family 9 := level9.get ⟨49,by decide⟩
def sourceMap1274 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1274 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1274_checked : acceptsGraphIso
    (source (graph core1274) (root 9) 0 1) DegreeOneSmallSpectrum1108.graph sourceMap1274=true := by decide +kernel
theorem fusedMap1274_checked : acceptsGraphIso
    (fused (graph core1274) (root 9) 0 1) DegreeOneSmallSpectrum871.graph fusedMap1274=true := by decide +kernel
theorem certified1274 : Certified (graph core1274) (root 9) 0 1 :=
  of_native_maps core1274 DegreeOneSmallSpectrum1108.graph DegreeOneSmallSpectrum871.graph
    sourceMap1274 fusedMap1274 sourceMap1274_checked fusedMap1274_checked
    DegreeOneSmallComparisons.comparison1274
#print axioms sourceMap1274_checked
#print axioms fusedMap1274_checked
#print axioms certified1274
def sourceMap1274swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1274swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1274swap_checked : acceptsGraphIso
    (source (graph core1274) (root 9) 1 0) DegreeOneSmallSpectrum1108.graph sourceMap1274swap=true := by decide +kernel
theorem fusedMap1274swap_checked : acceptsGraphIso
    (fused (graph core1274) (root 9) 1 0) DegreeOneSmallSpectrum871.graph fusedMap1274swap=true := by decide +kernel
theorem certified1274swap : Certified (graph core1274) (root 9) 1 0 :=
  of_native_maps core1274 DegreeOneSmallSpectrum1108.graph DegreeOneSmallSpectrum871.graph
    sourceMap1274swap fusedMap1274swap sourceMap1274swap_checked fusedMap1274swap_checked
    DegreeOneSmallComparisons.comparison1274
#print axioms sourceMap1274swap_checked
#print axioms fusedMap1274swap_checked
#print axioms certified1274swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
