/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1372 : Family 9 := level9.get ⟨118,by decide⟩
def sourceMap1372 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1372 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1372_checked : acceptsGraphIso
    (source (graph core1372) (root 9) 0 1) DegreeOneSmallSpectrum1435.graph sourceMap1372=true := by decide +kernel
theorem fusedMap1372_checked : acceptsGraphIso
    (fused (graph core1372) (root 9) 0 1) DegreeOneSmallSpectrum973.graph fusedMap1372=true := by decide +kernel
theorem certified1372 : Certified (graph core1372) (root 9) 0 1 :=
  of_native_maps core1372 DegreeOneSmallSpectrum1435.graph DegreeOneSmallSpectrum973.graph
    sourceMap1372 fusedMap1372 sourceMap1372_checked fusedMap1372_checked
    DegreeOneSmallComparisons.comparison1372
#print axioms sourceMap1372_checked
#print axioms fusedMap1372_checked
#print axioms certified1372
def sourceMap1372swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1372swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1372swap_checked : acceptsGraphIso
    (source (graph core1372) (root 9) 1 0) DegreeOneSmallSpectrum1435.graph sourceMap1372swap=true := by decide +kernel
theorem fusedMap1372swap_checked : acceptsGraphIso
    (fused (graph core1372) (root 9) 1 0) DegreeOneSmallSpectrum973.graph fusedMap1372swap=true := by decide +kernel
theorem certified1372swap : Certified (graph core1372) (root 9) 1 0 :=
  of_native_maps core1372 DegreeOneSmallSpectrum1435.graph DegreeOneSmallSpectrum973.graph
    sourceMap1372swap fusedMap1372swap sourceMap1372swap_checked fusedMap1372swap_checked
    DegreeOneSmallComparisons.comparison1372
#print axioms sourceMap1372swap_checked
#print axioms fusedMap1372swap_checked
#print axioms certified1372swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
