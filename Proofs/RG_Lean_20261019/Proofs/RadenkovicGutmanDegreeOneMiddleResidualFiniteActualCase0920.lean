/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0920 : Family 10 := level10.get ⟨715,by decide⟩
def sourceMap0920 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0920 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0920_checked : acceptsGraphIso
    (source (graph core0920) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2183.graph sourceMap0920=true := by decide +kernel
theorem fusedMap0920_checked : acceptsGraphIso
    (fused (graph core0920) (root 10) 2 2) DegreeTwoThreeSpectrum5461.graph fusedMap0920=true := by decide +kernel
theorem certified0920 : Certified (graph core0920) (root 10) 2 2 :=
  of_native_maps core0920 DegreeOneMiddleResidualSpectrum2183.graph DegreeTwoThreeSpectrum5461.graph
    sourceMap0920 fusedMap0920 sourceMap0920_checked fusedMap0920_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0920
#print axioms sourceMap0920_checked
#print axioms fusedMap0920_checked
#print axioms certified0920
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
