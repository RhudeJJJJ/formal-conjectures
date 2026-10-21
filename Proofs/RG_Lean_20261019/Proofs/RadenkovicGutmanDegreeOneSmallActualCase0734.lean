/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0734 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0734 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 1 2 v)
def fusedMap0734 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0734_checked : acceptsGraphIso
    (source (graph core0734) (root 7) 1 2) DegreeOneSmallSpectrum1522.graph sourceMap0734=true := by decide +kernel
theorem fusedMap0734_checked : acceptsGraphIso
    (fused (graph core0734) (root 7) 1 2) DegreeOneSmallSpectrum979.graph fusedMap0734=true := by decide +kernel
theorem certified0734 : Certified (graph core0734) (root 7) 1 2 :=
  of_native_maps core0734 DegreeOneSmallSpectrum1522.graph DegreeOneSmallSpectrum979.graph
    sourceMap0734 fusedMap0734 sourceMap0734_checked fusedMap0734_checked
    DegreeOneSmallComparisons.comparison0734
#print axioms sourceMap0734_checked
#print axioms fusedMap0734_checked
#print axioms certified0734
def sourceMap0734swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,8,9] (sourceLabel 7 2 1 v)
def fusedMap0734swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0734swap_checked : acceptsGraphIso
    (source (graph core0734) (root 7) 2 1) DegreeOneSmallSpectrum1522.graph sourceMap0734swap=true := by decide +kernel
theorem fusedMap0734swap_checked : acceptsGraphIso
    (fused (graph core0734) (root 7) 2 1) DegreeOneSmallSpectrum979.graph fusedMap0734swap=true := by decide +kernel
theorem certified0734swap : Certified (graph core0734) (root 7) 2 1 :=
  of_native_maps core0734 DegreeOneSmallSpectrum1522.graph DegreeOneSmallSpectrum979.graph
    sourceMap0734swap fusedMap0734swap sourceMap0734swap_checked fusedMap0734swap_checked
    DegreeOneSmallComparisons.comparison0734
#print axioms sourceMap0734swap_checked
#print axioms fusedMap0734swap_checked
#print axioms certified0734swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
