/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0195 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0195 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap0195 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap0195_checked : acceptsGraphIso
    (source (graph core0195) (root 4) 4 4) DegreeOneMiddleResidualSpectrum258.graph sourceMap0195=true := by decide +kernel
theorem fusedMap0195_checked : acceptsGraphIso
    (fused (graph core0195) (root 4) 4 4) DegreeTwoThreeSpectrum2309.graph fusedMap0195=true := by decide +kernel
theorem certified0195 : Certified (graph core0195) (root 4) 4 4 :=
  of_native_maps core0195 DegreeOneMiddleResidualSpectrum258.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap0195 fusedMap0195 sourceMap0195_checked fusedMap0195_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0195
#print axioms sourceMap0195_checked
#print axioms fusedMap0195_checked
#print axioms certified0195
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
