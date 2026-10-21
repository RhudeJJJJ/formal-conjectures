/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1632 : Family 9 := level9.get ⟨374,by decide⟩
def sourceMap1632 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1632 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1632_checked : acceptsGraphIso
    (source (graph core1632) (root 9) 0 1) DegreeOneSmallSpectrum1829.graph sourceMap1632=true := by decide +kernel
theorem fusedMap1632_checked : acceptsGraphIso
    (fused (graph core1632) (root 9) 0 1) DegreeOneSmallSpectrum1136.graph fusedMap1632=true := by decide +kernel
theorem certified1632 : Certified (graph core1632) (root 9) 0 1 :=
  of_native_maps core1632 DegreeOneSmallSpectrum1829.graph DegreeOneSmallSpectrum1136.graph
    sourceMap1632 fusedMap1632 sourceMap1632_checked fusedMap1632_checked
    DegreeOneSmallComparisons.comparison1632
#print axioms sourceMap1632_checked
#print axioms fusedMap1632_checked
#print axioms certified1632
def sourceMap1632swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1632swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1632swap_checked : acceptsGraphIso
    (source (graph core1632) (root 9) 1 0) DegreeOneSmallSpectrum1829.graph sourceMap1632swap=true := by decide +kernel
theorem fusedMap1632swap_checked : acceptsGraphIso
    (fused (graph core1632) (root 9) 1 0) DegreeOneSmallSpectrum1136.graph fusedMap1632swap=true := by decide +kernel
theorem certified1632swap : Certified (graph core1632) (root 9) 1 0 :=
  of_native_maps core1632 DegreeOneSmallSpectrum1829.graph DegreeOneSmallSpectrum1136.graph
    sourceMap1632swap fusedMap1632swap sourceMap1632swap_checked fusedMap1632swap_checked
    DegreeOneSmallComparisons.comparison1632
#print axioms sourceMap1632swap_checked
#print axioms fusedMap1632swap_checked
#print axioms certified1632swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
