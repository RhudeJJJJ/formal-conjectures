/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0950 : Family 10 := level10.get ⟨773,by decide⟩
def sourceMap0950 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0950 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0950_checked : acceptsGraphIso
    (source (graph core0950) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2237.graph sourceMap0950=true := by decide +kernel
theorem fusedMap0950_checked : acceptsGraphIso
    (fused (graph core0950) (root 10) 2 2) DegreeTwoThreeSpectrum5550.graph fusedMap0950=true := by decide +kernel
theorem certified0950 : Certified (graph core0950) (root 10) 2 2 :=
  of_native_maps core0950 DegreeOneMiddleResidualSpectrum2237.graph DegreeTwoThreeSpectrum5550.graph
    sourceMap0950 fusedMap0950 sourceMap0950_checked fusedMap0950_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0950
#print axioms sourceMap0950_checked
#print axioms fusedMap0950_checked
#print axioms certified0950
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
