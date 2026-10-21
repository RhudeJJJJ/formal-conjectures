/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1648 : Family 9 := level9.get ⟨391,by decide⟩
def sourceMap1648 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1648 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1648_checked : acceptsGraphIso
    (source (graph core1648) (root 9) 0 1) DegreeOneSmallSpectrum1872.graph sourceMap1648=true := by decide +kernel
theorem fusedMap1648_checked : acceptsGraphIso
    (fused (graph core1648) (root 9) 0 1) DegreeOneSmallSpectrum1191.graph fusedMap1648=true := by decide +kernel
theorem certified1648 : Certified (graph core1648) (root 9) 0 1 :=
  of_native_maps core1648 DegreeOneSmallSpectrum1872.graph DegreeOneSmallSpectrum1191.graph
    sourceMap1648 fusedMap1648 sourceMap1648_checked fusedMap1648_checked
    DegreeOneSmallComparisons.comparison1648
#print axioms sourceMap1648_checked
#print axioms fusedMap1648_checked
#print axioms certified1648
def sourceMap1648swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1648swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1648swap_checked : acceptsGraphIso
    (source (graph core1648) (root 9) 1 0) DegreeOneSmallSpectrum1872.graph sourceMap1648swap=true := by decide +kernel
theorem fusedMap1648swap_checked : acceptsGraphIso
    (fused (graph core1648) (root 9) 1 0) DegreeOneSmallSpectrum1191.graph fusedMap1648swap=true := by decide +kernel
theorem certified1648swap : Certified (graph core1648) (root 9) 1 0 :=
  of_native_maps core1648 DegreeOneSmallSpectrum1872.graph DegreeOneSmallSpectrum1191.graph
    sourceMap1648swap fusedMap1648swap sourceMap1648swap_checked fusedMap1648swap_checked
    DegreeOneSmallComparisons.comparison1648
#print axioms sourceMap1648swap_checked
#print axioms fusedMap1648swap_checked
#print axioms certified1648swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
