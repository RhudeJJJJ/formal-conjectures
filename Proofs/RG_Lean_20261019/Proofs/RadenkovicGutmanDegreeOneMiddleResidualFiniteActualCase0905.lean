/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0905 : Family 10 := level10.get ⟨691,by decide⟩
def sourceMap0905 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0905 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0905_checked : acceptsGraphIso
    (source (graph core0905) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2160.graph sourceMap0905=true := by decide +kernel
theorem fusedMap0905_checked : acceptsGraphIso
    (fused (graph core0905) (root 10) 2 2) DegreeTwoThreeSpectrum5427.graph fusedMap0905=true := by decide +kernel
theorem certified0905 : Certified (graph core0905) (root 10) 2 2 :=
  of_native_maps core0905 DegreeOneMiddleResidualSpectrum2160.graph DegreeTwoThreeSpectrum5427.graph
    sourceMap0905 fusedMap0905 sourceMap0905_checked fusedMap0905_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0905
#print axioms sourceMap0905_checked
#print axioms fusedMap0905_checked
#print axioms certified0905
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
