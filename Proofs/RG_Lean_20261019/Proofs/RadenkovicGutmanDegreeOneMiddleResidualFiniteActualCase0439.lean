/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0439 : Family 9 := level9.get ⟨439,by decide⟩
def sourceMap0439 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0439 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0439_checked : acceptsGraphIso
    (source (graph core0439) (root 9) 2 2) DegreeOneMiddleResidualSpectrum836.graph sourceMap0439=true := by decide +kernel
theorem fusedMap0439_checked : acceptsGraphIso
    (fused (graph core0439) (root 9) 2 2) DegreeTwoThreeSpectrum4442.graph fusedMap0439=true := by decide +kernel
theorem certified0439 : Certified (graph core0439) (root 9) 2 2 :=
  of_native_maps core0439 DegreeOneMiddleResidualSpectrum836.graph DegreeTwoThreeSpectrum4442.graph
    sourceMap0439 fusedMap0439 sourceMap0439_checked fusedMap0439_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0439
#print axioms sourceMap0439_checked
#print axioms fusedMap0439_checked
#print axioms certified0439
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
