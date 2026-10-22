/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0092 : Family 8 := level8.get ⟨42,by decide⟩
def sourceMap0092 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0092 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0092_checked : acceptsGraphIso
    (source (graph core0092) (root 8) 2 2) DegreeOneMiddleResidualSpectrum288.graph sourceMap0092=true := by decide +kernel
theorem fusedMap0092_checked : acceptsGraphIso
    (fused (graph core0092) (root 8) 2 2) DegreeTwoThreeSpectrum2324.graph fusedMap0092=true := by decide +kernel
theorem certified0092 : Certified (graph core0092) (root 8) 2 2 :=
  of_native_maps core0092 DegreeOneMiddleResidualSpectrum288.graph DegreeTwoThreeSpectrum2324.graph
    sourceMap0092 fusedMap0092 sourceMap0092_checked fusedMap0092_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0092
#print axioms sourceMap0092_checked
#print axioms fusedMap0092_checked
#print axioms certified0092
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
