/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0246 : Family 9 := level9.get ⟨60,by decide⟩
def sourceMap0246 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0246 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0246_checked : acceptsGraphIso
    (source (graph core0246) (root 9) 2 2) DegreeOneMiddleResidualSpectrum628.graph sourceMap0246=true := by decide +kernel
theorem fusedMap0246_checked : acceptsGraphIso
    (fused (graph core0246) (root 9) 2 2) DegreeTwoThreeSpectrum3963.graph fusedMap0246=true := by decide +kernel
theorem certified0246 : Certified (graph core0246) (root 9) 2 2 :=
  of_native_maps core0246 DegreeOneMiddleResidualSpectrum628.graph DegreeTwoThreeSpectrum3963.graph
    sourceMap0246 fusedMap0246 sourceMap0246_checked fusedMap0246_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0246
#print axioms sourceMap0246_checked
#print axioms fusedMap0246_checked
#print axioms certified0246
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
