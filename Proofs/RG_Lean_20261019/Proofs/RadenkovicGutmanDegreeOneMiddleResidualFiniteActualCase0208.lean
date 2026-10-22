/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0208 : Family 9 := level9.get ⟨11,by decide⟩
def sourceMap0208 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0208 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0208_checked : acceptsGraphIso
    (source (graph core0208) (root 9) 2 2) DegreeOneMiddleResidualSpectrum627.graph sourceMap0208=true := by decide +kernel
theorem fusedMap0208_checked : acceptsGraphIso
    (fused (graph core0208) (root 9) 2 2) DegreeTwoThreeSpectrum3856.graph fusedMap0208=true := by decide +kernel
theorem certified0208 : Certified (graph core0208) (root 9) 2 2 :=
  of_native_maps core0208 DegreeOneMiddleResidualSpectrum627.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap0208 fusedMap0208 sourceMap0208_checked fusedMap0208_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0208
#print axioms sourceMap0208_checked
#print axioms fusedMap0208_checked
#print axioms certified0208
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
