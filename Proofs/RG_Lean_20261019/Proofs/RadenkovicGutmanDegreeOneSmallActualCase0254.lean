/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0254 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0254 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 2 3 v)
def fusedMap0254 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0254_checked : acceptsGraphIso
    (source (graph core0254) (root 5) 2 3) DegreeOneSmallSpectrum1365.graph sourceMap0254=true := by decide +kernel
theorem fusedMap0254_checked : acceptsGraphIso
    (fused (graph core0254) (root 5) 2 3) DegreeOneSmallSpectrum922.graph fusedMap0254=true := by decide +kernel
theorem certified0254 : Certified (graph core0254) (root 5) 2 3 :=
  of_native_maps core0254 DegreeOneSmallSpectrum1365.graph DegreeOneSmallSpectrum922.graph
    sourceMap0254 fusedMap0254 sourceMap0254_checked fusedMap0254_checked
    DegreeOneSmallComparisons.comparison0254
#print axioms sourceMap0254_checked
#print axioms fusedMap0254_checked
#print axioms certified0254
def sourceMap0254swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 5 3 2 v)
def fusedMap0254swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0254swap_checked : acceptsGraphIso
    (source (graph core0254) (root 5) 3 2) DegreeOneSmallSpectrum1365.graph sourceMap0254swap=true := by decide +kernel
theorem fusedMap0254swap_checked : acceptsGraphIso
    (fused (graph core0254) (root 5) 3 2) DegreeOneSmallSpectrum922.graph fusedMap0254swap=true := by decide +kernel
theorem certified0254swap : Certified (graph core0254) (root 5) 3 2 :=
  of_native_maps core0254 DegreeOneSmallSpectrum1365.graph DegreeOneSmallSpectrum922.graph
    sourceMap0254swap fusedMap0254swap sourceMap0254swap_checked fusedMap0254swap_checked
    DegreeOneSmallComparisons.comparison0254
#print axioms sourceMap0254swap_checked
#print axioms fusedMap0254swap_checked
#print axioms certified0254swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
