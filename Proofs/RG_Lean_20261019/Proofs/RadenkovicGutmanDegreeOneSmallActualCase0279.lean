/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0279 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0279 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0279 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0279_checked : acceptsGraphIso
    (source (graph core0279) (root 6) 0 3) DegreeOneSmallSpectrum377.graph sourceMap0279=true := by decide +kernel
theorem fusedMap0279_checked : acceptsGraphIso
    (fused (graph core0279) (root 6) 0 3) DegreeOneSmallSpectrum378.graph fusedMap0279=true := by decide +kernel
theorem certified0279 : Certified (graph core0279) (root 6) 0 3 :=
  of_native_maps core0279 DegreeOneSmallSpectrum377.graph DegreeOneSmallSpectrum378.graph
    sourceMap0279 fusedMap0279 sourceMap0279_checked fusedMap0279_checked
    DegreeOneSmallComparisons.comparison0279
#print axioms sourceMap0279_checked
#print axioms fusedMap0279_checked
#print axioms certified0279
def sourceMap0279swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0279swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0279swap_checked : acceptsGraphIso
    (source (graph core0279) (root 6) 3 0) DegreeOneSmallSpectrum377.graph sourceMap0279swap=true := by decide +kernel
theorem fusedMap0279swap_checked : acceptsGraphIso
    (fused (graph core0279) (root 6) 3 0) DegreeOneSmallSpectrum378.graph fusedMap0279swap=true := by decide +kernel
theorem certified0279swap : Certified (graph core0279) (root 6) 3 0 :=
  of_native_maps core0279 DegreeOneSmallSpectrum377.graph DegreeOneSmallSpectrum378.graph
    sourceMap0279swap fusedMap0279swap sourceMap0279swap_checked fusedMap0279swap_checked
    DegreeOneSmallComparisons.comparison0279
#print axioms sourceMap0279swap_checked
#print axioms fusedMap0279swap_checked
#print axioms certified0279swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
