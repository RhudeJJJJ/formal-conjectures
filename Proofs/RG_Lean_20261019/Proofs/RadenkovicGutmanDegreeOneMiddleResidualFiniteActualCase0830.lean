/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0830 : Family 10 := level10.get ⟨539,by decide⟩
def sourceMap0830 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0830 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0830_checked : acceptsGraphIso
    (source (graph core0830) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2029.graph sourceMap0830=true := by decide +kernel
theorem fusedMap0830_checked : acceptsGraphIso
    (fused (graph core0830) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1104.graph fusedMap0830=true := by decide +kernel
theorem certified0830 : Certified (graph core0830) (root 10) 2 2 :=
  of_native_maps core0830 DegreeOneMiddleResidualSpectrum2029.graph DegreeOneMiddleResidualSpectrum1104.graph
    sourceMap0830 fusedMap0830 sourceMap0830_checked fusedMap0830_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0830
#print axioms sourceMap0830_checked
#print axioms fusedMap0830_checked
#print axioms certified0830
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
