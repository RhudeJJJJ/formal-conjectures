/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0257 : Family 9 := level9.get ⟨76,by decide⟩
def sourceMap0257 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0257 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0257_checked : acceptsGraphIso
    (source (graph core0257) (root 9) 2 2) DegreeOneMiddleResidualSpectrum665.graph sourceMap0257=true := by decide +kernel
theorem fusedMap0257_checked : acceptsGraphIso
    (fused (graph core0257) (root 9) 2 2) DegreeTwoThreeSpectrum4012.graph fusedMap0257=true := by decide +kernel
theorem certified0257 : Certified (graph core0257) (root 9) 2 2 :=
  of_native_maps core0257 DegreeOneMiddleResidualSpectrum665.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap0257 fusedMap0257 sourceMap0257_checked fusedMap0257_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0257
#print axioms sourceMap0257_checked
#print axioms fusedMap0257_checked
#print axioms certified0257
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
