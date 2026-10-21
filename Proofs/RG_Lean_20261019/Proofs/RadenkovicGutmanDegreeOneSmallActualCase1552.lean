/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1552 : Family 9 := level9.get ⟨279,by decide⟩
def sourceMap1552 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1552 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1552_checked : acceptsGraphIso
    (source (graph core1552) (root 9) 0 1) DegreeOneSmallSpectrum1417.graph sourceMap1552=true := by decide +kernel
theorem fusedMap1552_checked : acceptsGraphIso
    (fused (graph core1552) (root 9) 0 1) DegreeOneSmallSpectrum1507.graph fusedMap1552=true := by decide +kernel
theorem certified1552 : Certified (graph core1552) (root 9) 0 1 :=
  of_native_maps core1552 DegreeOneSmallSpectrum1417.graph DegreeOneSmallSpectrum1507.graph
    sourceMap1552 fusedMap1552 sourceMap1552_checked fusedMap1552_checked
    DegreeOneSmallComparisons.comparison1552
#print axioms sourceMap1552_checked
#print axioms fusedMap1552_checked
#print axioms certified1552
def sourceMap1552swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1552swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1552swap_checked : acceptsGraphIso
    (source (graph core1552) (root 9) 1 0) DegreeOneSmallSpectrum1417.graph sourceMap1552swap=true := by decide +kernel
theorem fusedMap1552swap_checked : acceptsGraphIso
    (fused (graph core1552) (root 9) 1 0) DegreeOneSmallSpectrum1507.graph fusedMap1552swap=true := by decide +kernel
theorem certified1552swap : Certified (graph core1552) (root 9) 1 0 :=
  of_native_maps core1552 DegreeOneSmallSpectrum1417.graph DegreeOneSmallSpectrum1507.graph
    sourceMap1552swap fusedMap1552swap sourceMap1552swap_checked fusedMap1552swap_checked
    DegreeOneSmallComparisons.comparison1552
#print axioms sourceMap1552swap_checked
#print axioms fusedMap1552swap_checked
#print axioms certified1552swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
