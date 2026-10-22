/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0987 : Family 10 := level10.get ⟨858,by decide⟩
def sourceMap0987 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0987 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0987_checked : acceptsGraphIso
    (source (graph core0987) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2289.graph sourceMap0987=true := by decide +kernel
theorem fusedMap0987_checked : acceptsGraphIso
    (fused (graph core0987) (root 10) 2 2) DegreeTwoThreeSpectrum5694.graph fusedMap0987=true := by decide +kernel
theorem certified0987 : Certified (graph core0987) (root 10) 2 2 :=
  of_native_maps core0987 DegreeOneMiddleResidualSpectrum2289.graph DegreeTwoThreeSpectrum5694.graph
    sourceMap0987 fusedMap0987 sourceMap0987_checked fusedMap0987_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0987
#print axioms sourceMap0987_checked
#print axioms fusedMap0987_checked
#print axioms certified0987
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
