/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1638 : Family 9 := level9.get ⟨378,by decide⟩
def sourceMap1638 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1638 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1638_checked : acceptsGraphIso
    (source (graph core1638) (root 9) 0 1) DegreeOneSmallSpectrum1832.graph sourceMap1638=true := by decide +kernel
theorem fusedMap1638_checked : acceptsGraphIso
    (fused (graph core1638) (root 9) 0 1) DegreeOneSmallSpectrum1143.graph fusedMap1638=true := by decide +kernel
theorem certified1638 : Certified (graph core1638) (root 9) 0 1 :=
  of_native_maps core1638 DegreeOneSmallSpectrum1832.graph DegreeOneSmallSpectrum1143.graph
    sourceMap1638 fusedMap1638 sourceMap1638_checked fusedMap1638_checked
    DegreeOneSmallComparisons.comparison1638
#print axioms sourceMap1638_checked
#print axioms fusedMap1638_checked
#print axioms certified1638
def sourceMap1638swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1638swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1638swap_checked : acceptsGraphIso
    (source (graph core1638) (root 9) 1 0) DegreeOneSmallSpectrum1832.graph sourceMap1638swap=true := by decide +kernel
theorem fusedMap1638swap_checked : acceptsGraphIso
    (fused (graph core1638) (root 9) 1 0) DegreeOneSmallSpectrum1143.graph fusedMap1638swap=true := by decide +kernel
theorem certified1638swap : Certified (graph core1638) (root 9) 1 0 :=
  of_native_maps core1638 DegreeOneSmallSpectrum1832.graph DegreeOneSmallSpectrum1143.graph
    sourceMap1638swap fusedMap1638swap sourceMap1638swap_checked fusedMap1638swap_checked
    DegreeOneSmallComparisons.comparison1638
#print axioms sourceMap1638swap_checked
#print axioms fusedMap1638swap_checked
#print axioms certified1638swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
