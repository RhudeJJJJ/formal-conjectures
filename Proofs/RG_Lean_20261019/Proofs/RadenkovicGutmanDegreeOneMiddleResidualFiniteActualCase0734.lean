/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0734 : Family 10 := level10.get ⟨359,by decide⟩
def sourceMap0734 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0734 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0734_checked : acceptsGraphIso
    (source (graph core0734) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1827.graph sourceMap0734=true := by decide +kernel
theorem fusedMap0734_checked : acceptsGraphIso
    (fused (graph core0734) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1358.graph fusedMap0734=true := by decide +kernel
theorem certified0734 : Certified (graph core0734) (root 10) 2 2 :=
  of_native_maps core0734 DegreeOneMiddleResidualSpectrum1827.graph DegreeOneMiddleResidualSpectrum1358.graph
    sourceMap0734 fusedMap0734 sourceMap0734_checked fusedMap0734_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0734
#print axioms sourceMap0734_checked
#print axioms fusedMap0734_checked
#print axioms certified0734
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
