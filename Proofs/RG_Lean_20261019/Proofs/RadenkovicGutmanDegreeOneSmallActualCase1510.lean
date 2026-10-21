/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1510 : Family 9 := level9.get ⟨239,by decide⟩
def sourceMap1510 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1510 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1510_checked : acceptsGraphIso
    (source (graph core1510) (root 9) 0 1) DegreeOneSmallSpectrum1396.graph sourceMap1510=true := by decide +kernel
theorem fusedMap1510_checked : acceptsGraphIso
    (fused (graph core1510) (root 9) 0 1) DegreeOneSmallSpectrum1452.graph fusedMap1510=true := by decide +kernel
theorem certified1510 : Certified (graph core1510) (root 9) 0 1 :=
  of_native_maps core1510 DegreeOneSmallSpectrum1396.graph DegreeOneSmallSpectrum1452.graph
    sourceMap1510 fusedMap1510 sourceMap1510_checked fusedMap1510_checked
    DegreeOneSmallComparisons.comparison1510
#print axioms sourceMap1510_checked
#print axioms fusedMap1510_checked
#print axioms certified1510
def sourceMap1510swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1510swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1510swap_checked : acceptsGraphIso
    (source (graph core1510) (root 9) 1 0) DegreeOneSmallSpectrum1396.graph sourceMap1510swap=true := by decide +kernel
theorem fusedMap1510swap_checked : acceptsGraphIso
    (fused (graph core1510) (root 9) 1 0) DegreeOneSmallSpectrum1452.graph fusedMap1510swap=true := by decide +kernel
theorem certified1510swap : Certified (graph core1510) (root 9) 1 0 :=
  of_native_maps core1510 DegreeOneSmallSpectrum1396.graph DegreeOneSmallSpectrum1452.graph
    sourceMap1510swap fusedMap1510swap sourceMap1510swap_checked fusedMap1510swap_checked
    DegreeOneSmallComparisons.comparison1510
#print axioms sourceMap1510swap_checked
#print axioms fusedMap1510swap_checked
#print axioms certified1510swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
