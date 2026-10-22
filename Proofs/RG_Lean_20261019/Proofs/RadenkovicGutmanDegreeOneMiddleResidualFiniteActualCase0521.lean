/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0521 : Family 10 := level10.get ⟨42,by decide⟩
def sourceMap0521 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0521 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap0521_checked : acceptsGraphIso
    (source (graph core0521) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1372.graph sourceMap0521=true := by decide +kernel
theorem fusedMap0521_checked : acceptsGraphIso
    (fused (graph core0521) (root 10) 2 2) DegreeTwoThreeSpectrum5123.graph fusedMap0521=true := by decide +kernel
theorem certified0521 : Certified (graph core0521) (root 10) 2 2 :=
  of_native_maps core0521 DegreeOneMiddleResidualSpectrum1372.graph DegreeTwoThreeSpectrum5123.graph
    sourceMap0521 fusedMap0521 sourceMap0521_checked fusedMap0521_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0521
#print axioms sourceMap0521_checked
#print axioms fusedMap0521_checked
#print axioms certified0521
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
