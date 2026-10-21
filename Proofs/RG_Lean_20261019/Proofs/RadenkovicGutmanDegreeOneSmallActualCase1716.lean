/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1716 : Family 9 := level9.get ⟨495,by decide⟩
def sourceMap1716 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1716 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1716_checked : acceptsGraphIso
    (source (graph core1716) (root 9) 0 1) DegreeOneSmallSpectrum1968.graph sourceMap1716=true := by decide +kernel
theorem fusedMap1716_checked : acceptsGraphIso
    (fused (graph core1716) (root 9) 0 1) DegreeOneSmallSpectrum1469.graph fusedMap1716=true := by decide +kernel
theorem certified1716 : Certified (graph core1716) (root 9) 0 1 :=
  of_native_maps core1716 DegreeOneSmallSpectrum1968.graph DegreeOneSmallSpectrum1469.graph
    sourceMap1716 fusedMap1716 sourceMap1716_checked fusedMap1716_checked
    DegreeOneSmallComparisons.comparison1716
#print axioms sourceMap1716_checked
#print axioms fusedMap1716_checked
#print axioms certified1716
def sourceMap1716swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1716swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1716swap_checked : acceptsGraphIso
    (source (graph core1716) (root 9) 1 0) DegreeOneSmallSpectrum1968.graph sourceMap1716swap=true := by decide +kernel
theorem fusedMap1716swap_checked : acceptsGraphIso
    (fused (graph core1716) (root 9) 1 0) DegreeOneSmallSpectrum1469.graph fusedMap1716swap=true := by decide +kernel
theorem certified1716swap : Certified (graph core1716) (root 9) 1 0 :=
  of_native_maps core1716 DegreeOneSmallSpectrum1968.graph DegreeOneSmallSpectrum1469.graph
    sourceMap1716swap fusedMap1716swap sourceMap1716swap_checked fusedMap1716swap_checked
    DegreeOneSmallComparisons.comparison1716
#print axioms sourceMap1716swap_checked
#print axioms fusedMap1716swap_checked
#print axioms certified1716swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
