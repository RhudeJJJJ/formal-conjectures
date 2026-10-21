/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0391 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0391 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0391 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0391_checked : acceptsGraphIso
    (source (graph core0391) (root 6) 1 3) DegreeOneSmallSpectrum993.graph sourceMap0391=true := by decide +kernel
theorem fusedMap0391_checked : acceptsGraphIso
    (fused (graph core0391) (root 6) 1 3) DegreeOneSmallSpectrum862.graph fusedMap0391=true := by decide +kernel
theorem certified0391 : Certified (graph core0391) (root 6) 1 3 :=
  of_native_maps core0391 DegreeOneSmallSpectrum993.graph DegreeOneSmallSpectrum862.graph
    sourceMap0391 fusedMap0391 sourceMap0391_checked fusedMap0391_checked
    DegreeOneSmallComparisons.comparison0391
#print axioms sourceMap0391_checked
#print axioms fusedMap0391_checked
#print axioms certified0391
def sourceMap0391swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,7,8] (sourceLabel 6 3 1 v)
def fusedMap0391swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0391swap_checked : acceptsGraphIso
    (source (graph core0391) (root 6) 3 1) DegreeOneSmallSpectrum993.graph sourceMap0391swap=true := by decide +kernel
theorem fusedMap0391swap_checked : acceptsGraphIso
    (fused (graph core0391) (root 6) 3 1) DegreeOneSmallSpectrum862.graph fusedMap0391swap=true := by decide +kernel
theorem certified0391swap : Certified (graph core0391) (root 6) 3 1 :=
  of_native_maps core0391 DegreeOneSmallSpectrum993.graph DegreeOneSmallSpectrum862.graph
    sourceMap0391swap fusedMap0391swap sourceMap0391swap_checked fusedMap0391swap_checked
    DegreeOneSmallComparisons.comparison0391
#print axioms sourceMap0391swap_checked
#print axioms fusedMap0391swap_checked
#print axioms certified0391swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
