/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0986 : Family 10 := level10.get ⟨856,by decide⟩
def sourceMap0986 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0986 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0986_checked : acceptsGraphIso
    (source (graph core0986) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2288.graph sourceMap0986=true := by decide +kernel
theorem fusedMap0986_checked : acceptsGraphIso
    (fused (graph core0986) (root 10) 2 2) DegreeTwoThreeSpectrum5692.graph fusedMap0986=true := by decide +kernel
theorem certified0986 : Certified (graph core0986) (root 10) 2 2 :=
  of_native_maps core0986 DegreeOneMiddleResidualSpectrum2288.graph DegreeTwoThreeSpectrum5692.graph
    sourceMap0986 fusedMap0986 sourceMap0986_checked fusedMap0986_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0986
#print axioms sourceMap0986_checked
#print axioms fusedMap0986_checked
#print axioms certified0986
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
