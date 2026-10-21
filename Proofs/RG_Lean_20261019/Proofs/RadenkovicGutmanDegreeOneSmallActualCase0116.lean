/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0116 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0116 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap0116 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap0116_checked : acceptsGraphIso
    (source (graph core0116) (root 4) 0 5) DegreeOneSmallSpectrum372.graph sourceMap0116=true := by decide +kernel
theorem fusedMap0116_checked : acceptsGraphIso
    (fused (graph core0116) (root 4) 0 5) DegreeOneSmallSpectrum378.graph fusedMap0116=true := by decide +kernel
theorem certified0116 : Certified (graph core0116) (root 4) 0 5 :=
  of_native_maps core0116 DegreeOneSmallSpectrum372.graph DegreeOneSmallSpectrum378.graph
    sourceMap0116 fusedMap0116 sourceMap0116_checked fusedMap0116_checked
    DegreeOneSmallComparisons.comparison0116
#print axioms sourceMap0116_checked
#print axioms fusedMap0116_checked
#print axioms certified0116
def sourceMap0116swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,11,6] (sourceLabel 4 5 0 v)
def fusedMap0116swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap0116swap_checked : acceptsGraphIso
    (source (graph core0116) (root 4) 5 0) DegreeOneSmallSpectrum372.graph sourceMap0116swap=true := by decide +kernel
theorem fusedMap0116swap_checked : acceptsGraphIso
    (fused (graph core0116) (root 4) 5 0) DegreeOneSmallSpectrum378.graph fusedMap0116swap=true := by decide +kernel
theorem certified0116swap : Certified (graph core0116) (root 4) 5 0 :=
  of_native_maps core0116 DegreeOneSmallSpectrum372.graph DegreeOneSmallSpectrum378.graph
    sourceMap0116swap fusedMap0116swap sourceMap0116swap_checked fusedMap0116swap_checked
    DegreeOneSmallComparisons.comparison0116
#print axioms sourceMap0116swap_checked
#print axioms fusedMap0116swap_checked
#print axioms certified0116swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
