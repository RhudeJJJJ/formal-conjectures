/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1734 : Family 9 := level9.get ⟨551,by decide⟩
def sourceMap1734 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1734 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1734_checked : acceptsGraphIso
    (source (graph core1734) (root 9) 0 1) DegreeOneSmallSpectrum1562.graph sourceMap1734=true := by decide +kernel
theorem fusedMap1734_checked : acceptsGraphIso
    (fused (graph core1734) (root 9) 0 1) DegreeOneSmallSpectrum1563.graph fusedMap1734=true := by decide +kernel
theorem certified1734 : Certified (graph core1734) (root 9) 0 1 :=
  of_native_maps core1734 DegreeOneSmallSpectrum1562.graph DegreeOneSmallSpectrum1563.graph
    sourceMap1734 fusedMap1734 sourceMap1734_checked fusedMap1734_checked
    DegreeOneSmallComparisons.comparison1734
#print axioms sourceMap1734_checked
#print axioms fusedMap1734_checked
#print axioms certified1734
def sourceMap1734swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1734swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1734swap_checked : acceptsGraphIso
    (source (graph core1734) (root 9) 1 0) DegreeOneSmallSpectrum1562.graph sourceMap1734swap=true := by decide +kernel
theorem fusedMap1734swap_checked : acceptsGraphIso
    (fused (graph core1734) (root 9) 1 0) DegreeOneSmallSpectrum1563.graph fusedMap1734swap=true := by decide +kernel
theorem certified1734swap : Certified (graph core1734) (root 9) 1 0 :=
  of_native_maps core1734 DegreeOneSmallSpectrum1562.graph DegreeOneSmallSpectrum1563.graph
    sourceMap1734swap fusedMap1734swap sourceMap1734swap_checked fusedMap1734swap_checked
    DegreeOneSmallComparisons.comparison1734
#print axioms sourceMap1734swap_checked
#print axioms fusedMap1734swap_checked
#print axioms certified1734swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
