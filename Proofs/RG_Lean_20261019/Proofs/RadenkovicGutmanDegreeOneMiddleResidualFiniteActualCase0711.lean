/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0711 : Family 10 := level10.get ⟨324,by decide⟩
def sourceMap0711 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0711 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0711_checked : acceptsGraphIso
    (source (graph core0711) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1791.graph sourceMap0711=true := by decide +kernel
theorem fusedMap0711_checked : acceptsGraphIso
    (fused (graph core0711) (root 10) 2 2) DegreeTwoThreeSpectrum5549.graph fusedMap0711=true := by decide +kernel
theorem certified0711 : Certified (graph core0711) (root 10) 2 2 :=
  of_native_maps core0711 DegreeOneMiddleResidualSpectrum1791.graph DegreeTwoThreeSpectrum5549.graph
    sourceMap0711 fusedMap0711 sourceMap0711_checked fusedMap0711_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0711
#print axioms sourceMap0711_checked
#print axioms fusedMap0711_checked
#print axioms certified0711
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
